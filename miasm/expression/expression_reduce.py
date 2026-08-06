"""
Expression reducer:
Apply reduction rules to an Expression ast
"""

import logging
from typing import Any, Callable, Protocol, cast
from miasm.expression.expression import Expr, ExprInt, ExprId, ExprLoc, ExprOp, \
    ExprSlice, ExprCompose, ExprMem, ExprCond, is_compose, is_op, is_slice

log_reduce = logging.getLogger("expr_reduce")
console_handler = logging.StreamHandler()
console_handler.setFormatter(logging.Formatter("[%(levelname)-8s]: %(message)s"))
log_reduce.addHandler(console_handler)
log_reduce.setLevel(logging.WARNING)



class ExprNode[T](object):
    """Clone of Expression object with additional information"""
    _expr: Expr
    info: T|None

    def __init__(self, expr: Expr):
        self._expr = expr

    @property
    def expr(self) -> Expr:
        return self._expr

class ExprNodeInt[T](ExprNode[T]):
    arg: None
    
    def __init__(self, expr: Expr):
        assert expr.is_int()
        super(ExprNodeInt, self).__init__(expr)
        self.arg = None

    @property
    def expr(self) -> ExprInt:
        return cast(ExprInt, self._expr)

    def __repr__(self):
        if self.info is not None:
            out = repr(self.info)
        else:
            out = str(self.expr)
        return out


class ExprNodeId[T](ExprNode[T]):
    arg: None

    def __init__(self, expr: Expr):
        assert expr.is_id()
        super(ExprNodeId, self).__init__(expr)
        self.arg = None

    @property
    def expr(self) -> ExprId:
        return cast(ExprId, self._expr)

    def __repr__(self):
        if self.info is not None:
            out = repr(self.info)
        else:
            out = str(self.expr)
        return out


class ExprNodeLoc[T](ExprNode[T]):
    arg: None

    def __init__(self, expr: Expr):
        assert expr.is_loc()
        super(ExprNodeLoc, self).__init__(expr)
        self.arg = None
    
    @property
    def expr(self) -> ExprLoc:
        return cast(ExprLoc, self._expr)

    def __repr__(self):
        if self.info is not None:
            out = repr(self.info)
        else:
            out = str(self.expr)
        return out


class ExprNodeMem[T](ExprNode[T]):
    ptr: ExprNode[T]|None

    def __init__(self, expr: Expr):
        assert expr.is_mem()
        super(ExprNodeMem, self).__init__(expr)
        self.ptr = None
    
    @property
    def expr(self) -> ExprMem:
        return cast(ExprMem, self._expr)

    def __repr__(self):
        if self.info is not None:
            out = repr(self.info)
        else:
            out = "@%d[%r]" % (self.expr.size, self.ptr)
        return out


class ExprNodeOp[T](ExprNode[T]):
    args: list[ExprNode[T]]|None

    def __init__(self, expr: ExprOp):
        assert expr.is_op()
        super(ExprNodeOp, self).__init__(expr)
        self.args = None

    @property
    def expr(self) -> ExprOp:
        return cast(ExprOp, self._expr)

    def __repr__(self):
        assert self.args is not None
        assert is_op(self.expr)
        if self.info is not None:
            out = repr(self.info)
        else:
            if len(self.args) == 1:
                out = "(%s(%r))" % (self.expr.op, self.args[0])
            else:
                out = "(%s)" % self.expr.op.join(repr(arg) for arg in self.args)
        return out


class ExprNodeSlice[T](ExprNode[T]):
    arg: ExprNode[T]|None

    def __init__(self, expr: ExprSlice):
        super(ExprNodeSlice, self).__init__(expr)
        self.arg = None

    @property
    def expr(self) -> ExprSlice:
        return cast(ExprSlice, self._expr)

    def __repr__(self):
        assert is_slice(self.expr)
        if self.info is not None:
            out = repr(self.info)
        else:
            out = "%r[%d:%d]" % (self.arg, self.expr.start, self.expr.stop)
        return out


class ExprNodeCompose[T](ExprNode[T]):
    args: list[ExprNode[T]]|None

    def __init__(self, expr: ExprCompose):
        super(ExprNodeCompose, self).__init__(expr)
        self.args = None

    @property
    def expr(self) -> ExprCompose:
        return cast(ExprCompose, self._expr)

    def __repr__(self):
        assert is_compose(self.expr) and self.args is not None
        if self.info is not None:
            out = repr(self.info)
        else:
            out = "{%s}" % ', '.join(repr(arg) for arg in self.args)
        return out


class ExprNodeCond[T](ExprNode[T]):
    cond: ExprNode[T]|None
    src1: ExprNode[T]|None
    src2: ExprNode[T]|None

    def __init__(self, expr: ExprCond):
        super(ExprNodeCond, self).__init__(expr)
        self.cond = None
        self.src1 = None
        self.src2 = None

    @property
    def expr(self) -> ExprCond:
        return cast(ExprCond, self._expr)

    def __repr__(self):
        if self.info is not None:
            out = repr(self.info)
        else:
            out = "(%r?%r:%r)" % (self.cond, self.src1, self.src2)
        return out

class Rule[T](Protocol):
    def __call__(
        self,
        reducer: "ExprReducer[T]",
        node: ExprNode[T],
        lvl: int = 0,
        **kwargs,
    ) -> T|None: ...

class ExprReducer[T](object):
    """Apply reduction rules to an expr

    reduction_rules: list of ordered reduction rules

    List of function representing reduction rules
    Function API:
    reduction_xxx(self, node, lvl=0)
    with:
    * node: the ExprNode to qualify
    * lvl: [optional] the recursion level
    Returns:
    * None if the reduction rule is not applied
    * the resulting information to store in the ExprNode.info

    allow_none_result: allow missing reduction rules
    """

    reduction_rules: list[Rule[T]] = []
    allow_none_result = False

    def expr2node(self, expr: Expr) -> ExprNode[T]:
        """Build ExprNode mirror of @expr

        @expr: Expression to analyze
        """

        if isinstance(expr, ExprId):
            node = ExprNodeId[T](expr)
        elif isinstance(expr, ExprLoc):
            node = ExprNodeLoc[T](expr)
        elif isinstance(expr, ExprInt):
            node = ExprNodeInt[T](expr)
        elif isinstance(expr, ExprMem):
            son = self.expr2node(expr.ptr)
            node = ExprNodeMem[T](expr)
            node.ptr = son
        elif isinstance(expr, ExprSlice):
            son = self.expr2node(expr.arg)
            node = ExprNodeSlice[T](expr)
            node.arg = son
        elif isinstance(expr, ExprOp):
            sons = [self.expr2node(arg) for arg in expr.args]
            node = ExprNodeOp[T](expr)
            node.args = sons
        elif isinstance(expr, ExprCompose):
            sons = [self.expr2node(arg) for arg in expr.args]
            node = ExprNodeCompose[T](expr)
            node.args = sons
        elif isinstance(expr, ExprCond):
            node = ExprNodeCond[T](expr)
            node.cond = self.expr2node(expr.cond)
            node.src1 = self.expr2node(expr.src1)
            node.src2 = self.expr2node(expr.src2)
        else:
            raise TypeError("Unknown Expr Type %r", type(expr))
        return node

    def reduce(self, expr: Expr, **kwargs) -> ExprNode[T]:
        """Returns an ExprNode tree mirroring @expr tree. The ExprNode is
        computed by applying reduction rules to the expression @expr

        @expr: an Expression
        """

        node = self.expr2node(expr)
        return self.categorize(node, lvl=0, **kwargs)

    def categorize(self, node: ExprNode[T], lvl=0, **kwargs) -> ExprNode[T]:
        """Recursively apply rules to @node

        @node: ExprNode to analyze
        @lvl: actual recursion level
        """

        log_reduce.debug("\t" * lvl + "Reduce...: %s", node.expr)
        if isinstance(node, ExprNodeId):
            node = ExprNodeId(node.expr)
        elif isinstance(node, ExprNodeInt):
            node = ExprNodeInt(node.expr)
        elif isinstance(node, ExprNodeLoc):
            node = ExprNodeLoc(node.expr)
        elif isinstance(node, ExprNodeMem):
            assert node.ptr is not None
            ptr = self.categorize(node.ptr, lvl=lvl + 1, **kwargs)
            node = ExprNodeMem(ExprMem(ptr.expr, node.expr.size))
            node.ptr = ptr
        elif isinstance(node, ExprNodeSlice):
            assert node.arg is not None
            arg = self.categorize(node.arg, lvl=lvl + 1, **kwargs)
            node = ExprNodeSlice(ExprSlice(arg.expr, node.expr.start, node.expr.stop))
            node.arg = arg
        elif isinstance(node, ExprNodeOp):
            assert node.args is not None
            new_args = []
            for arg in node.args:
                new_a = self.categorize(arg, lvl=lvl + 1, **kwargs)
                assert new_a.expr.size == arg.expr.size
                new_args.append(new_a)
            node = ExprNodeOp(ExprOp(node.expr.op, *[x.expr for x in new_args]))
            node.args = new_args
            expr = node.expr
        elif isinstance(node, ExprNodeCompose):
            assert node.args is not None
            new_args: list[ExprNode[T]] = []
            new_expr_args: list[Expr] = []
            for arg in node.args:
                arg = self.categorize(arg, lvl=lvl + 1, **kwargs)
                new_args.append(arg)
                new_expr_args.append(arg.expr)
            new_expr = ExprCompose(*new_expr_args)
            node = ExprNodeCompose(new_expr)
            node.args = new_args
        elif isinstance(node, ExprNodeCond):
            assert node.cond is not None and node.src1 is not None and node.src2 is not None
            cond = self.categorize(node.cond, lvl=lvl + 1, **kwargs)
            src1 = self.categorize(node.src1, lvl=lvl + 1, **kwargs)
            src2 = self.categorize(node.src2, lvl=lvl + 1, **kwargs)
            node = ExprNodeCond(ExprCond(cond.expr, src1.expr, src2.expr))
            node.cond, node.src1, node.src2 = cond, src1, src2
        else:
            raise TypeError("Unknown Expr Type %r", type(node.expr))

        node.info = self.apply_rules(node, lvl=lvl, **kwargs)
        log_reduce.debug("\t" * lvl + "Reduce result: %s %r",
                         node.expr, node.info)
        return node

    def apply_rules(self, node: ExprNode[T], lvl=0, **kwargs) -> T|None:
        """Find and apply reduction rules to @node

        @node: ExprNode to analyse
        @lvl: actuel recursion level
        """

        for rule in self.reduction_rules:
            ret = rule(self, node, lvl=lvl, **kwargs)

            if ret is not None:
                log_reduce.debug("\t" * lvl + "Rule found: %r", rule)
                return ret
        if not self.allow_none_result:
            raise RuntimeError('Missing reduction rule for %r' % node.expr)
