from typing import Literal

from heapq import merge

from miasm.expression.expression import Expr, ExprId, ExprCond, ExprOp, LocKey, is_cond, is_id, is_op
from miasm.ir.ir import IRBlock, AssignBlock, Lifter
from miasm.analysis.data_flow import DiGraphLivenessSSA
from miasm.analysis.ssa import SSADiGraph, get_phi_sources_parent_block, \
    irblock_has_phi

class Varinfo(object):
    """Store liveness information for a variable"""
    __slots__ = ["live_index", "loc_key", "index"]

    def __init__(self, live_index, loc_key, index):
        self.live_index = live_index
        self.loc_key = loc_key
        self.index = index


class UnSSADiGraph(object):
    """
    Implements unssa algorithm
    Revisiting Out-of-SSA Translation for Correctness, Code Quality, and
    Efficiency
    """

    def __init__(self, ssa: SSADiGraph, head: LocKey, lifter: Lifter):
        self.ssa = ssa
        self.head = head

        # Set of created variables
        self.copy_vars = set[ExprId]()
        # Virtual parallel copies

        # On loc_key's Phi node dst -> set((parent, src))
        self.phi_parent_sources: dict[Expr, set[tuple[LocKey, ExprId]]] = {}
        # On loc_key's Phi node, loc_key -> set(Phi dsts)
        self.phi_destinations: dict[LocKey, set[ExprId]] = {}
        # Phi's dst -> result copy variable
        self.phi_new_var: dict[Expr, ExprId] = {}
        # Phi's dst -> {parent -> incoming copy variable}
        self.phi_pre_vars: dict[Expr, dict[LocKey, ExprId]] = {}
        # variable -> ordered congruence class
        self.merge_state: dict[ExprId, list[ExprId]] = {}

        # Launch the algorithm in several steps
        self.isolate_phi_nodes_block()
        self.insert_parallel_copy()
        self.liveness = DiGraphLivenessSSA(ssa.graph)
        self.liveness.init_var_info(lifter)
        self.liveness.compute_liveness()
        self.order_ssa_var_dom()
        self.init_phis_merge_state()
        self.aggressive_coalesce_block()
        self.replace_merge_sets()   
        self.remove_phi()
        self.remove_assign_eq()

    def insert_parallel_copy(self):
        """
        Materialize CSSA with distinct copies for every Phi input and result.
        """
        ircfg = self.ssa.graph
        parent_to_parallel_copies: dict[LocKey, dict[ExprId, Expr]] = {}

        for block_loc in list(ircfg.blocks.keys()):
            irblock = ircfg.get_block(block_loc)
            if not irblock or not irblock_has_phi(irblock):
                continue

            phis: dict[ExprId, ExprOp] = {}
            post_copies: dict[Expr, ExprId] = {}
            for dst in self.phi_destinations[irblock.loc_key]:
                post_var = self.phi_new_var[dst]
                pre_vars: list[ExprId] = []
                for parent, src in self.phi_parent_sources[dst]:
                    pre_var = self.phi_pre_vars[dst][parent]
                    pre_vars.append(pre_var)
                    parent_to_parallel_copies.setdefault(parent, {})[pre_var] = src
                phis[post_var] = ExprOp('Phi', *pre_vars)
                post_copies[dst] = post_var

            assignblks = list(irblock)
            assignblks[0] = AssignBlock(phis, irblock[0].instr)
            assignblks.insert(1, AssignBlock(post_copies, irblock[0].instr))
            new_irblock = IRBlock(irblock.loc_db, irblock.loc_key, assignblks)
            ircfg.blocks[irblock.loc_key] = new_irblock

        for parent_loc, parallel_copies in parent_to_parallel_copies.items():
            parent = ircfg.blocks[parent_loc]
            assignblks = list(parent)
            jmp_block = parent[-1]

            phi_conds = dict()
            for jmp_dst, jmp_src in jmp_block.items():
                if jmp_dst != ircfg.IRDst:
                    continue

                jmp_read_values = set(filter(lambda expr: is_id(expr), jmp_src.get_r(mem_read=True)))
                jmp_read_values = list(jmp_read_values)
                if len(jmp_read_values) == 0:
                    continue
                if not is_cond(jmp_src):
                    continue

                if len(jmp_read_values) == 1 and is_id(jmp_read_values[0]) and jmp_read_values[0].name.startswith("PhiCond"):
                    continue

                id_expr = ExprId("PhiCond%s_%d_%d" % (
                    parent_loc, len(phi_conds), jmp_src.cond.size
                ), jmp_src.cond.size)
                phi_conds[id_expr] = jmp_src.cond

                dst_count = 0
                for dst in jmp_block.keys():
                    if dst == ircfg.IRDst:
                        dst_count += 1
                        continue
                    phi_conds[dst] = jmp_block[dst]
                assert dst_count == 1

                repl_cond = ExprCond(id_expr, jmp_src.src1, jmp_src.src2)
                assignblks.insert(-1, AssignBlock(phi_conds, jmp_block.instr))
                assignblks[-1] = AssignBlock({ircfg.IRDst: repl_cond}, jmp_block.instr)

            assignblks.insert(-1, AssignBlock(parallel_copies, jmp_block.instr))
            ircfg.blocks[parent_loc] = IRBlock(parent.loc_db, parent.loc_key, assignblks)

    def create_copy_var(self, var: Expr) -> ExprId:
        """
        Generate a new var standing for @var
        @var: variable to replace
        """
        new_var = ExprId('var%d' % len(self.copy_vars), var.size)
        self.copy_vars.add(new_var)
        return new_var

    def isolate_phi_nodes_block(self):
        """
        Allocate one incoming copy per Phi edge and one result copy per Phi.
        """
        ircfg = self.ssa.graph
        for irblock in ircfg.blocks.values():
            if not irblock_has_phi(irblock):
                continue
            for dst, sources in irblock[0].items():
                assert is_op(sources, 'Phi')
                new_var = self.create_copy_var(dst)
                self.phi_new_var[dst] = new_var

                var_to_parents = get_phi_sources_parent_block(
                    self.ssa.graph,
                    irblock.loc_key,
                    sources.args
                )

                for src in sources.args:
                    assert is_id(src)
                    parents = var_to_parents[src]
                    for parent in parents:
                        self.phi_parent_sources.setdefault(dst, set()).add((parent, src))
                        self.phi_pre_vars.setdefault(dst, {})[parent] = self.create_copy_var(dst)

            self.phi_destinations[irblock.loc_key] = set(irblock[0]) # type: ignore

    def init_phis_merge_state(self):
        """
        Coalesce the virtual incoming and result copies of each Phi.
        """
        for dst, post_var in self.phi_new_var.items():
            merge_set = [post_var] + list(self.phi_pre_vars[dst].values())
            merge_set.sort(key=lambda var: self.var_to_varinfo[var].live_index)
            for var in merge_set:
                self.merge_state[var] = merge_set

    def order_ssa_var_dom(self):
        """Compute dominance order of each ssa variable"""
        ircfg = self.ssa.graph

        # Pre-DFS intervals give constant-time block dominance tests.
        dominator_tree = ircfg.compute_dominator_tree(self.head)
        self.dom_pre = {}
        self.dom_end = {}
        order: list[LocKey] = []
        todo = [(self.head, False)]
        while todo:
            loc_key, closing = todo.pop()
            if closing:
                self.dom_end[loc_key] = len(order)
                continue
            self.dom_pre[loc_key] = len(order)
            order.append(loc_key)
            todo.append((loc_key, True))
            todo.extend((child, False) for child in reversed(
                dominator_tree.successors(loc_key)
            ))

        # variable -> Varinfo
        self.var_to_varinfo: dict[Expr, Varinfo] = {}
        # live_index orders definitions inside the block pre-DFS traversal.
        live_index = 0

        for loc_key in order:
            irblock = ircfg.blocks.get(loc_key, None)
            if irblock is None:
                continue

            # Number all definitions, including the virtual copies.
            for index, assignblk in enumerate(irblock):
                used = False
                for dst in assignblk:
                    if not dst.is_id():
                        continue
                    if dst in self.ssa.immutable_ids:
                        # Will not be considered by the current algo, ignore it
                        # (for instance, IRDst)
                        continue

                    assert dst not in self.var_to_varinfo
                    self.var_to_varinfo[dst] = Varinfo(live_index, loc_key, index)
                    used = True
                if used:
                    live_index += 1

    def ssa_def_dominates(self, node_a: Expr, node_b: Expr) -> bool:
        """Test definition dominance, including order inside a block."""
        info_a = self.var_to_varinfo[node_a]
        info_b = self.var_to_varinfo[node_b]
        if info_a.loc_key == info_b.loc_key:
            return info_a.live_index <= info_b.live_index
        return (self.dom_pre[info_a.loc_key] <= self.dom_pre[info_b.loc_key] <
                self.dom_end[info_a.loc_key])


    def ssa_def_is_live_at(self, node_a: Expr, node_b: Expr) -> bool:
        """
        Return True if @node_a is live after @node_b's definition.

        @parent is retained for callers; CSSA liveness models the edge copies.
        """
        info_b = self.var_to_varinfo[node_b]
        return node_a in self.liveness.blocks[info_b.loc_key].infos[info_b.index].var_out

    def merge_nodes_interfere(self, node_a: Expr, node_b: Expr) -> bool:
        """
        Return True if @node_a and @node_b interfere
        @node_a: variable
        @node_b: variable
        @parent: Optional parent location of the phi source for liveness tests

        Interference check is: is x live at y definition (or reverse)
        TODO: add Value-based interference improvement
        """
        if self.var_to_varinfo[node_a].live_index == self.var_to_varinfo[node_b].live_index:
            # Defined in the same AssignBlock -> interfere
            return True

        if self.var_to_varinfo[node_a].live_index < self.var_to_varinfo[node_b].live_index:
            return self.ssa_def_is_live_at(node_a, node_b)
        return self.ssa_def_is_live_at(node_b, node_a)

    def merge_sets_interfere(self, merge_a: list[ExprId], merge_b: list[ExprId]) -> bool:
        """
        Apply Algorithm 2 to two pre-DFS-ordered congruence classes.

        @merge_a: pre-DFS-ordered list of equivalent variables
        @merge_b: pre-DFS-ordered list of equivalent variables
        @parent: retained for callers; CSSA liveness models the edge copies
        """
        if merge_a == merge_b:
            return False

        index_a = index_b = 0
        dom: list[tuple[Expr, Literal[1, 0]]] = []
        while index_a < len(merge_a) or index_b < len(merge_b):
            if index_a == len(merge_a):
                current, group = merge_b[index_b], 1
                index_b += 1
            elif index_b == len(merge_b):
                current, group = merge_a[index_a], 0
                index_a += 1
            elif (self.var_to_varinfo[merge_a[index_a]].live_index <
                  self.var_to_varinfo[merge_b[index_b]].live_index):
                current, group = merge_a[index_a], 0
                index_a += 1
            else:
                current, group = merge_b[index_b], 1
                index_b += 1

            while dom and not self.ssa_def_dominates(dom[-1][0], current):
                dom.pop()

            if (dom and dom[-1][1] != group and
                    self.merge_nodes_interfere(current, dom[-1][0])):
                return True
            dom.append((current, group))
        return False

    def aggressive_coalesce_parallel_copy(self, parallel_copies: dict[ExprId, ExprId]):
        """
        Try to coalesce variables each dst/src couple together from
        @parallel_copies

        @parallel_copies: a dictionary representing dst/src parallel
        assignments.
        """
        for dst, src in parallel_copies.items():
            dst_merge = self.merge_state.setdefault(dst, [dst])
            src_merge = self.merge_state.setdefault(src, [src])
            if not self.merge_sets_interfere(dst_merge, src_merge):
                merged = list(merge(
                    dst_merge, src_merge,
                    key=lambda var: self.var_to_varinfo[var].live_index
                ))
                for node in merged:
                    self.merge_state[node] = merged

    def aggressive_coalesce_block(self):
        """Try to coalesce phi var with their pre/post variables"""

        ircfg = self.ssa.graph

        # Run coalesce on the post phi parallel copy
        for irblock in ircfg.blocks.values():
            if not irblock_has_phi(irblock):
                continue
            parallel_copies: dict[ExprId, ExprId] = {}
            for dst in self.phi_destinations[irblock.loc_key]:
                parallel_copies[dst] = self.phi_new_var[dst]
            self.aggressive_coalesce_parallel_copy(parallel_copies)

            # Run coalesce on the pre phi parallel copy

            # Process affinities for the incoming copies already in parents.
            parent_to_parallel_copies: dict[LocKey, dict[ExprId, ExprId]] = {}
            for dst in self.phi_destinations[irblock.loc_key]:
                for parent, src in self.phi_parent_sources[dst]:
                    pre_var = self.phi_pre_vars[dst][parent]
                    parent_to_parallel_copies.setdefault(parent, {})[pre_var] = src

            for parent_parallel_copies in parent_to_parallel_copies.values():
                self.aggressive_coalesce_parallel_copy(parent_parallel_copies)

    def get_best_merge_set_name(self, merge_set: list[ExprId]) -> ExprId:
        """
        For a given @merge_set, prefer an original SSA variable instead of a
        created copy. In other case, take a random name.
        @merge_set: set of equivalent expressions
        """
        if not merge_set:
            raise RuntimeError("Merge set should not be empty")
        for var in merge_set:
            if var not in self.copy_vars:
                return var
        # select first name
        return merge_set[0]


    def replace_merge_sets(self):
        """
        In the graph, replace all variables from merge state by their
        representative variable
        """
        replace: dict[ExprId, ExprId] = {}
        merge_sets = set[frozenset[ExprId]]()

        # Elect representative for merge sets
        merge_set_to_name: dict[frozenset[ExprId], ExprId] = {}
        for merge_set in self.merge_state.values():
            frozen_merge_set = frozenset(merge_set)
            merge_sets.add(frozen_merge_set)
            var_name = self.get_best_merge_set_name(merge_set)
            merge_set_to_name[frozen_merge_set] = var_name

        # Generate replacement of variable by their representative
        for merge_set in merge_sets:
            var_name = merge_set_to_name[merge_set]
            merge_set = list(merge_set)
            for var in merge_set:
                replace[var] = var_name

        self.ssa.graph.simplify(lambda x: x.replace_expr(replace))

    def remove_phi(self):
        """
        Remove phi operators in @ifcfg
        @ircfg: IRDiGraph instance
        """

        for irblock in list(self.ssa.graph.blocks.values()):
            assignblks = list(irblock)
            out: dict[Expr, Expr] = {}
            for dst, src in assignblks[0].items():
                if is_op(src, 'Phi'):
                    assert set([dst]) == set(src.args)
                    continue
                out[dst] = src
            assignblks[0] = AssignBlock(out, assignblks[0].instr)
            self.ssa.graph.blocks[irblock.loc_key] = IRBlock(irblock.loc_db, irblock.loc_key, assignblks)

    def remove_assign_eq(self):
        """
        Remove trivial expressions (a=a) in the current graph
        """
        for irblock in list(self.ssa.graph.blocks.values()):
            assignblks = list(irblock)
            for i, assignblk in enumerate(assignblks):
                out: dict[Expr, Expr] = {}
                for dst, src in assignblk.items():
                    if dst == src:
                        continue
                    out[dst] = src
                assignblks[i] = AssignBlock(out, assignblk.instr)
            self.ssa.graph.blocks[irblock.loc_key] = IRBlock(irblock.loc_db, irblock.loc_key, assignblks)
