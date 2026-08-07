#                                                                              #
#                     Simplification methods library                           #
#                                                                              #

import logging
from typing import Callable, Type, cast

from future.utils import viewitems

from miasm.expression import simplifications_common
from miasm.expression import simplifications_cond
from miasm.expression import simplifications_explicit
from miasm.expression.expression_helper import fast_unify
import miasm.expression.expression as m2_expr
from miasm.expression.expression import ExprVisitorCallbackBottomToTop

# Expression Simplifier
# ---------------------

log_exprsimp = logging.getLogger("exprsimp")
console_handler = logging.StreamHandler()
console_handler.setFormatter(logging.Formatter("[%(levelname)-8s]: %(message)s"))
log_exprsimp.addHandler(console_handler)
log_exprsimp.setLevel(logging.WARNING)


class ExpressionSimplifier(ExprVisitorCallbackBottomToTop):

    """Wrapper on expression simplification passes.

    Instance handle passes lists.

    Available passes lists are:
     - commons: common passes such as constant folding
     - heavy  : rare passes (for instance, in case of obfuscation)
    """

    type Simplifier[E: m2_expr.Expr] = Callable[
        ["ExpressionSimplifier", E],
        m2_expr.Expr,
    ]

    type ErasedSimplifier = Simplifier[m2_expr.Expr]

    # Common passes
    PASS_COMMON_OP: list[Simplifier[m2_expr.ExprOp]] = [
        simplifications_common.simp_cst_propagation,
        simplifications_common.simp_cond_op_int,
        simplifications_common.simp_cond_factor,
        simplifications_common.simp_add_multiple,
        # CC op
        simplifications_common.simp_cc_conds,
        simplifications_common.simp_subwc_cf,
        simplifications_common.simp_subwc_of,
        simplifications_common.simp_sign_subwc_cf,
        simplifications_common.simp_double_zeroext,
        simplifications_common.simp_double_signext,
        simplifications_common.simp_zeroext_eq_cst,
        simplifications_common.simp_ext_eq_ext,
        simplifications_common.simp_ext_cond_int,
        simplifications_common.simp_sub_cf_zero,

        simplifications_common.simp_cmp_int,
        simplifications_common.simp_cmp_bijective_op,
        simplifications_common.simp_sign_inf_zeroext,
        simplifications_common.simp_cmp_int_int,
        simplifications_common.simp_ext_cst,
        simplifications_common.simp_zeroext_and_cst_eq_cst,
        simplifications_common.simp_test_signext_inf,
        simplifications_common.simp_test_zeroext_inf,
        simplifications_common.simp_cond_inf_eq_unsigned_zero,
        simplifications_common.simp_compose_and_mask,
        simplifications_common.simp_bcdadd_cf,
        simplifications_common.simp_bcdadd,
        simplifications_common.simp_smod_sext,
        simplifications_common.simp_flag_cst,
    ]

    PASS_COMMON_SLICE: list[Simplifier[m2_expr.ExprSlice]] = [
        simplifications_common.simp_slice,
        simplifications_common.simp_slice_of_ext,
        simplifications_common.simp_slice_of_sext,
        simplifications_common.simp_slice_of_op_ext,
    ]

    PASS_COMMON_COMPOSE : list[Simplifier[m2_expr.ExprCompose]] = [simplifications_common.simp_compose]

    PASS_COMMON_COND: list[Simplifier[m2_expr.ExprCond]] = [
        simplifications_common.simp_cond,
        simplifications_common.simp_cond_zeroext,
        simplifications_common.simp_cond_add,
        # CC op
        simplifications_common.simp_cond_flag,
        simplifications_common.simp_cmp_int_arg,

        simplifications_common.simp_cond_eq_zero,
        simplifications_common.simp_x_and_cst_eq_cst,
        simplifications_common.simp_cond_logic_ext,
        simplifications_common.simp_cond_sign_bit,
        simplifications_common.simp_cond_eq_1_0,
        simplifications_common.simp_cond_cc_flag,
        simplifications_common.simp_cond_sub_cf,
    ]

    PASS_COMMON_MEM: list[Simplifier[m2_expr.ExprMem]] = [simplifications_common.simp_mem]

    # Cond passes
    PASS_COND_SLICE: list[Simplifier[m2_expr.ExprSlice]] = [
        simplifications_cond.expr_simp_inf_signed,
        simplifications_cond.expr_simp_inf_unsigned_inversed,
    ]

    PASS_COND_OP: list[Simplifier[m2_expr.ExprOp]] = [
        simplifications_cond.expr_simp_inverse,
    ]

    PASS_COND_COND: list[Simplifier[m2_expr.ExprCond]] = [
        simplifications_cond.expr_simp_equal
    ]


    # Available passes lists are:
    #  - highlevel: transform high level operators to explicit computations
    PASS_HIGH_TO_EXPLICIT_OP: list[Simplifier[m2_expr.ExprOp]] = [
        simplifications_explicit.simp_flags,
        simplifications_explicit.simp_ext,
    ]

    # Backward-compatible public pass maps
    PASS_COMMONS = {
        m2_expr.ExprOp: PASS_COMMON_OP,
        m2_expr.ExprSlice: PASS_COMMON_SLICE,
        m2_expr.ExprCompose: PASS_COMMON_COMPOSE,
        m2_expr.ExprCond: PASS_COMMON_COND,
        m2_expr.ExprMem: PASS_COMMON_MEM,
    }
    PASS_HEAVY = {}
    PASS_COND = {
        m2_expr.ExprSlice: PASS_COND_SLICE,
        m2_expr.ExprOp: PASS_COND_OP,
        m2_expr.ExprCond: PASS_COND_COND,
    }
    PASS_HIGH_TO_EXPLICIT = {
        m2_expr.ExprOp: PASS_HIGH_TO_EXPLICIT_OP,
    }

    expr_simp_cb: dict[Type[m2_expr.Expr], list[ErasedSimplifier]]

    def __init__(self):
        super(ExpressionSimplifier, self).__init__(self.expr_simp_inner)
        self.expr_simp_cb = {}

    def enable_passes(self, passes: dict):
        """Add passes from @passes
        @passes: dict(Expr class : list(callback))

        Callback signature: Expr callback(ExpressionSimplifier, Expr)
        """
        for current_type, current_passes in passes.items():
            self.enable_pass(current_type, current_passes)

    def enable_pass[E: m2_expr.Expr](self, expr_type: type[E], passes: list[Simplifier[E]]):
        """Add passes from @passes for ExprType @expr_type
        @expr_type: type[E]
        @passes: list(callback)

        Callback signature: Expr callback(ExpressionSimplifier, E)
        """

        # Clear cache of simplifiied expressions when adding a new pass
        self.cache.clear()

        self.expr_simp_cb.setdefault(expr_type, [])

        erased = [
            cast(ExpressionSimplifier.ErasedSimplifier, rule)
            for rule in passes
        ]
        self.expr_simp_cb[expr_type] = fast_unify(self.expr_simp_cb[expr_type] + erased)

    def apply_simp(self, expression: m2_expr.Expr) -> m2_expr.Expr:
        """Apply enabled simplifications on expression
        @expression: Expr instance
        Return an Expr instance"""

        cls = expression.__class__
        debug_level = log_exprsimp.level >= logging.DEBUG
        for simp_func in self.expr_simp_cb.get(cls, []):
            # Apply simplifications
            before = expression
            expression = simp_func(self, expression)
            after = expression

            if debug_level and before != after:
                log_exprsimp.debug("[%s] %s => %s", simp_func, before, after)

            # If class changes, stop to prevent wrong simplifications
            if expression.__class__ is not cls:
                break

        return expression

    def expr_simp_inner(self, expression: m2_expr.Expr) -> m2_expr.Expr:
        """Apply enabled simplifications on expression and find a stable state
        @expression: Expr instance
        Return an Expr instance"""

        # Find a stable state
        while True:
            # Canonize and simplify
            new_expr = self.apply_simp(expression.canonize())
            if new_expr == expression:
                return new_expr
            # Run recursively simplification on fresh new expression
            new_expr = self.visit(new_expr)
            expression = new_expr
        return new_expr

    def expr_simp(self, expression: m2_expr.Expr) -> m2_expr.Expr:
        "Call simplification recursively"
        return self.visit(expression)

    def __call__(self, expression: m2_expr.Expr) -> m2_expr.Expr:
        "Call simplification recursively"
        return self.visit(expression)

    def enable_common(self):
        self.enable_pass(m2_expr.ExprOp, self.PASS_COMMON_OP)
        self.enable_pass(m2_expr.ExprSlice, self.PASS_COMMON_SLICE)
        self.enable_pass(m2_expr.ExprCompose, self.PASS_COMMON_COMPOSE)
        self.enable_pass(m2_expr.ExprCond, self.PASS_COMMON_COND)
        self.enable_pass(m2_expr.ExprMem, self.PASS_COMMON_MEM)

    def enable_cond(self):
        self.enable_pass(m2_expr.ExprSlice, self.PASS_COND_SLICE)
        self.enable_pass(m2_expr.ExprOp, self.PASS_COND_OP)
        self.enable_pass(m2_expr.ExprCond, self.PASS_COND_COND)

    def enable_high_to_explicit(self):
        self.enable_pass(m2_expr.ExprOp, ExpressionSimplifier.PASS_HIGH_TO_EXPLICIT_OP)

# Public ExprSimplificationPass instance with commons passes
expr_simp = ExpressionSimplifier()
expr_simp.enable_common()

expr_simp_high_to_explicit = ExpressionSimplifier()
expr_simp_high_to_explicit.enable_high_to_explicit()

expr_simp_explicit = ExpressionSimplifier()
expr_simp_explicit.enable_common()
expr_simp_explicit.enable_high_to_explicit()
