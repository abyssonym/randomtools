from .utils import cached_property, read_lines_nocomment, summarize_state, \
                    utilrandom as random
from collections import defaultdict
from copy import deepcopy
from functools import total_ordering
from hashlib import md5
from itertools import product
from os import listdir, path
from sys import stdout
from time import time, sleep
import yaml


DEBUG = False
REDUCE = True
MODULE_FILEPATH, _ = path.split(__file__)
DEFAULT_CONFIG_FILENAME = path.join(MODULE_FILEPATH, 'default.doorrouter.yaml')


def log(line):
    if DEBUG or True:
        line = line.strip()
        print(line)
        stdout.flush()


class DoorRouterException(Exception):
    pass


class RollbackMixin:
    def commit(self, version=None):
        if not hasattr(self, '_rollback'):
            self._rollback = {}
        for attr in self.ROLLBACK_ATTRIBUTES:
            if not hasattr(self, attr):
                if (version, attr) in self._rollback:
                    del(self._rollback[version, attr])
                continue
            value = getattr(self, attr)
            if value is not None and not isinstance(value, Graph):
                value = type(value)(value)
            self._rollback[version, attr] = value

    def rollback(self, version=None):
        if not hasattr(self, '_rollback'):
            self._rollback = {}
        for attr in self.ROLLBACK_ATTRIBUTES:
            if (version, attr) not in self._rollback:
                if hasattr(self, attr):
                    delattr(self, attr)
                continue
            value = self._rollback[version, attr]
            if value is not None and not isinstance(value, Graph):
                value = type(value)(value)
            setattr(self, attr, value)


class Graph(RollbackMixin):
    ROLLBACK_ATTRIBUTES = {
        'all_edges', 'conditionless_edges',
        'nodes_by_rank', 'nodes_by_rank_or_less',
        '_reachable_from_root', '_root_reachable_from', '_double_rooted',
        '_bridge_cache',
        '_add_edge_options_cache',
        'conditional_nodes', 'reduced_graph',
        }

    @total_ordering
    class Node(RollbackMixin):
        ROLLBACK_ATTRIBUTES = {
            'edges', 'reverse_edges', 'rank',
            'guaranteed', 'full_guaranteed',
            '_rooted',
            '_reachable_cache',
            '_guaranteed_reachable_cache',
            '_free_travel_nodes', '_equivalent_nodes',
            '_free_travel_guaranteed', '_equivalent_guaranteed',
            }

        @total_ordering
        class Edge(RollbackMixin):
            ROLLBACK_ATTRIBUTES = {}
            GLOBAL_SORT_INDEX = 0

            def __init__(self, source, destination, condition, procedural,
                         update_caches):
                assert isinstance(source, Graph.Node)
                assert isinstance(destination, Graph.Node)
                assert isinstance(condition, frozenset)
                self.index = Graph.Node.Edge.GLOBAL_SORT_INDEX
                Graph.Node.Edge.GLOBAL_SORT_INDEX += 1

                self.source = source
                self.destination = destination
                self.generated = procedural
                graph = self.source.parent

                self.true_condition = set()
                self.false_condition = set()
                if condition:
                    if all(isinstance(l, str) for l in condition):
                        for l in condition:
                            if l.startswith('!'):
                                requirements = \
                                    graph.expand_requirements(l[1:])
                                assert len(requirements) == 1
                                for req in requirements:
                                    for node in req:
                                        node = \
                                            graph.get_by_label(node)
                                        assert isinstance(node, Graph.Node)
                                        self.false_condition.add(node)
                            else:
                                node = graph.get_by_label(l)
                                self.true_condition.add(node)
                            assert node is not None
                        self.true_condition = frozenset(self.true_condition)
                        self.false_condition = frozenset(self.false_condition)
                    else:
                        self.true_condition = frozenset(condition)
                    graph.conditional_nodes |= self.combined_conditions
                    for n in self.combined_conditions:
                        if not n.is_condition:
                            del(n._property_cache['is_condition'])
                    if self.true_condition:
                        self.source.parent.conditions.add(self.true_condition)
                    if self.false_condition:
                        self.source.parent.conditions.add(self.false_condition)
                assert self.__hash__() == self.signature.__hash__()

                self.enabled = True
                self.source.edges.add(self)
                self.destination.reverse_edges.add(self)
                graph.all_edges.add(self)
                if not self.combined_conditions:
                    graph.conditionless_edges.add(self)
                if update_caches and self.source.rooted:
                    graph.clear_rooted_cache()

                if self.false_condition:
                    raise NotImplementedError(
                        f'False conditions not supported with '
                        f'current optimizations: {self}')

                self.commit()

            def __repr__(self):
                if self.enabled:
                    return self.signature
                else:
                    return f'{self.signature} (DISABLED)'

            def __hash__(self):
                try:
                    return self._hash
                except AttributeError:
                    self._hash = self.signature.__hash__()
                return self.__hash__()

            def __eq__(self, other):
                return self.__hash__() == other.__hash__()

            def __lt__(self, other):
                return self.index < other.index

            @property
            def signature(self):
                if not self.false_condition:
                    s = (f'{self.source}->{self.destination}: '
                         f'{sorted(self.true_condition)}')
                else:
                    s = (f'{self.source}->{self.destination}: '
                         f'{sorted(self.true_condition)} '
                         f'!{sorted(self.false_condition)}')
                if self.generated:
                    s = f'{s}*'
                return s

            @property
            def rank(self):
                if self.source.rank is not None:
                    return self.source.rank
                return -1

            @cached_property
            def pair(self):
                candidates = {e for e in self.destination.edges if
                              e.destination is self.source and
                              e.true_condition == self.true_condition and
                              e.false_condition == self.false_condition and
                              e.generated == self.generated}
                if not candidates:
                    return None
                assert len(candidates) == 1
                pair = list(candidates)[0]
                return pair

            @property
            def soft_pairs(self):
                candidates = {e for e in self.destination.edges if
                              e.destination is self.source}
                if not candidates:
                    return None
                return candidates

            @cached_property
            def combined_conditions(self):
                return self.true_condition | self.false_condition

            @property
            def full_true_condition(self):
                return frozenset(
                        self.true_condition |
                        {n2 for n1 in self.true_condition
                         if n1.guaranteed for n2 in n1.guaranteed})

            @property
            def node_mapping(self):
                if hasattr(self.parent, 'node_mapping'):
                    return self.parent.node_mapping[self]

            def is_satisfied_by(self, nodes):
                if not self.enabled:
                    return False
                if self.true_condition and not (self.true_condition <= nodes):
                    return False
                if self.false_condition and self.false_condition <= nodes:
                    return False
                return True

            def is_full_satisfied_by(self, nodes, strict=True):
                '''
                if self.source.full_guaranteed is None:
                    return self.is_satisfied_by(nodes)
                for g in self.source.full_guaranteed:
                    if self.is_satisfied_by(g | nodes | self.source.guaranteed):
                        return True
                return False
                assert False
                '''
                if self.is_satisfied_by(nodes):
                    return True
                if self.source.guaranteed is None:
                    return False
                edges = {e for e in self.source.edges
                         if e.destination is self.destination}
                if strict and len(edges) <= 1:
                    return False
                full_guaranteed = set()
                for g in self.source.full_guaranteed:
                    result = False
                    for e in edges:
                        if e.is_satisfied_by(nodes | g):
                            result = True
                            guaranteed = frozenset(
                                g | e.full_true_condition |
                                self.source.guaranteed | {self.destination})
                            full_guaranteed.add(guaranteed)
                    if strict and not result:
                        return False
                    result = True
                if full_guaranteed:
                    return full_guaranteed
                return False

            def check_is_real_bridge(self):
                # accounts for conditions satisfied outside orphaned nodes
                # won't account for conditions outside of double-rooted sphere
                if not self.source.rooted:
                    return set()
                if self.source.rank is None:
                    return set()
                if self.destination.rank and \
                        self.source.rank >= self.destination.rank:
                    return set()
                done_edges = {self, self.pair}
                done_nodes = set()
                nodes = {self.destination}
                edges = set()
                if not self.is_satisfied_by(self.source.parent.double_rooted):
                    return set()
                while True:
                    test_nodes = nodes - done_nodes
                    for n in test_nodes:
                        edges |= n.reverse_edges
                    done_nodes |= nodes
                    test_edges = edges - done_edges
                    if not test_edges:
                        break
                    for e in test_edges:
                        done_edges.add(e)
                        if not e.is_satisfied_by(
                                self.source.parent.double_rooted):
                            continue
                        if e.source.rank is None:
                            continue
                        if e.source.rank is not None \
                                and e.source.rank <= self.source.rank:
                            return set()
                        nodes.add(e.source)
                return nodes

            def check_is_bridge(self):
                if self in self.source.parent._bridge_cache:
                    return self.source.parent._bridge_cache[self]
                nodes = self.check_is_real_bridge()
                self.source.parent._bridge_cache[self] = nodes
                return self.check_is_bridge()

            def get_bridge_double_orphanable(self):
                # very slow, accounts for ALL conditions
                rfr1, rrf1 = (self.source.parent.reachable_from_root,
                              self.source.parent.root_reachable_from)
                self.enabled = False
                self.source.parent.clear_rooted_cache()
                rfr2, rrf2 = (self.source.parent.reachable_from_root,
                              self.source.parent.root_reachable_from)
                self.enabled = True
                self.source.parent.clear_rooted_cache()
                assert rfr1 == self.source.parent.reachable_from_root
                assert rrf1 == self.source.parent.root_reachable_from
                return (rfr1-rfr2), (rrf1-rrf2)

            def remove(self):
                self.source.edges.remove(self)
                self.destination.reverse_edges.remove(self)
                self.source.parent.all_edges.remove(self)
                if not self.combined_conditions:
                    self.source.parent.conditionless_edges.remove(self)
                if self.source.rooted:
                    self.source.parent.clear_rooted_cache()

            def bidirectional_remove(self):
                self.remove()
                if self.pair and self.pair is not self:
                    self.pair.remove()

        def __init__(self, label, parent):
            LABEL_LENGTH_LIMIT = 8
            if len(label) > LABEL_LENGTH_LIMIT:
                raise Exception(f'Label {label} exceeds '
                                f'{LABEL_LENGTH_LIMIT} character limit.')
            self.label = label
            self.parent = parent
            if self.parent.root is not None:
                raise NotImplementedError("Can't do this apparently.")

            hashstr = 0
            for i, c in enumerate(label):
                c = ord(c)
                assert c & 0x80 == 0
                hashstr |= (c << (i * 7))
            hashvalue = 0
            md5str = f'{self.parent.seed}{label}'.encode('ascii')
            for c in md5(md5str).digest():
                hashvalue ^= c
            assert i < LABEL_LENGTH_LIMIT
            assert not ((0xff << (7 * LABEL_LENGTH_LIMIT)) & hashstr)
            hashstr |= (hashvalue << (7 * LABEL_LENGTH_LIMIT))
            hashstr.to_bytes(length=8)
            self._hash = hashstr
            self.sort_signature = self._hash

            self.rank = None
            self.force_bridge = set()

            self.edges = set()
            self.reverse_edges = set()
            self.parent.nodes.add(self)

            self.required_nodes = set()
            self.guarantee_nodes = set()
            self.twoway_conditions = set()
            self.guaranteed = None
            self.full_guaranteed = None

            self.commit()

        def __repr__(self):
            return self.label

        def __hash__(self):
            return self._hash

        def __eq__(self, other):
            if self is other:
                return True
            assert isinstance(other, Graph.Node)
            if self.parent is not other.parent:
                return False
            assert self.label != other.label
            return False

        def __lt__(self, other):
            return self.label < other.label

        @property
        def double_edges(self):
            return self.edges | self.reverse_edges

        @property
        def rooted(self):
            if hasattr(self, '_rooted'):
                return self._rooted
            return False

        @cached_property
        def is_connectable_node(self):
            return self in self.parent.connectable

        @cached_property
        def is_condition(self):
            return self in self.parent.conditional_nodes

        @cached_property
        def is_guarantee_condition(self):
            return self in self.parent.guarantee_nodes

        @property
        def is_interesting(self):
            return self in self.parent.interesting_nodes

        @cached_property
        def local_conditional_nodes(self):
            return {c for e in self.edges for c in e.combined_conditions}

        @property
        def reverse_nodes(self):
            return {e.source for e in self.reverse_edges} | {self}

        @property
        def free_travel_nodes(self):
            if hasattr(self, '_free_travel_nodes'):
                return self._free_travel_nodes
            free_travel_nodes = frozenset(self.get_free_travel_nodes())
            assert self in free_travel_nodes
            for n in free_travel_nodes:
                n._free_travel_nodes = free_travel_nodes
            return self.free_travel_nodes

        @property
        def equivalent_nodes(self):
            if not hasattr(self.parent, '_reachable_from_root'):
                return self.free_travel_nodes
            if hasattr(self, '_equivalent_nodes'):
                return self._equivalent_nodes
            equivalent_nodes = frozenset(self.get_equivalent_nodes())
            assert self in equivalent_nodes
            for n in equivalent_nodes:
                n._equivalent_nodes = equivalent_nodes
            return self.equivalent_nodes

        @property
        def free_travel_guaranteed(self):
            if hasattr(self, '_free_travel_guaranteed'):
                return self._free_travel_guaranteed
            guaranteed = frozenset.union(
                *[n.guaranteed for n in self.free_travel_nodes])
            for n in self.free_travel_nodes:
                n._free_travel_guaranteed = guaranteed
            return self.free_travel_guaranteed

        @property
        def equivalent_guaranteed(self):
            if not hasattr(self.parent, '_reachable_from_root'):
                return self.free_travel_guaranteed
            if hasattr(self, '_equivalent_guaranteed'):
                return self._equivalent_guaranteed
            if self.guaranteed is None:
                for n in self.equivalent_nodes:
                    assert n.guaranteed is None
                    n._equivalent_guaranteed = None
            else:
                guaranteed = frozenset.union(
                    *[n.guaranteed for n in self.equivalent_nodes])
                for n in self.equivalent_nodes:
                    n._equivalent_guaranteed = guaranteed
            return self.equivalent_guaranteed

        @property
        def generated_edges(self):
            return {e for e in self.all_edges if e.generated}

        def get_by_label(self, label):
            return self.parent.get_by_label(label)

        def by_label(self, label):
            return self.get_by_label(label)

        def add_edge(self, other, condition=None, procedural=False,
                     update_caches=True):
            if condition is None:
                condition = frozenset(set())
            else:
                assert isinstance(condition, frozenset)

            edge = self.Edge(self, other, condition, procedural=procedural,
                             update_caches=update_caches)
            return edge

        def add_edges(self, other, conditions, procedural=False,
                      simplify=True, update_caches=True):
            for condition in sorted(conditions, key=lambda c: sorted(c)):
                self.add_edge(other, condition, procedural=procedural,
                              update_caches=update_caches)
            if simplify:
                self.simplify_edges()

        def simplify_edges(self):
            for edge1 in list(self.edges):
                for edge2 in list(self.edges):
                    if edge1 not in self.edges or edge2 not in self.edges:
                        continue
                    if edge1 is edge2:
                        continue
                    if edge1.destination is not edge2.destination:
                        continue
                    if edge1.false_condition >= edge2.false_condition and \
                            edge1.true_condition <= edge2.true_condition:
                        self.edges.remove(edge2)
                        self.parent.all_edges.remove(edge2)

        def simplify_full_guaranteed(self):
            self.full_guaranteed = {g & self.parent.conditional_nodes
                                    for g in self.full_guaranteed}
            if len(self.full_guaranteed) < 3:
                return
            smallers, biggers = set(), set()
            for g1 in self.full_guaranteed:
                for g2 in self.full_guaranteed:
                    if g1 < g2:
                        smallers.add(g1)
                        biggers.add(g2)
            self.full_guaranteed = self.full_guaranteed - (smallers & biggers)

        def get_orphanable_guaranteed(self):
            # accurate and fastest if guarantees can be guaranteed
            return {n for n in self.parent.rooted
                    if self in n.guaranteed}

        def get_orphanable(self):
            result = self.get_orphanable_guaranteed()
            for n in result:
                if n is not self:
                    assert n.rank > self.rank
            return result

        def add_guarantee(self, other):
            assert isinstance(other, Graph.Node)
            if self.parent.config['lazy_complex_nodes']:
                self.required_nodes.add(other)
            else:
                self.guarantee_nodes.add(other)
                self.parent.guarantee_nodes.add(other)
                self.local_conditional_nodes.add(other)

        def add_twoway_condition(self, condition):
            assert '!' not in condition
            if isinstance(condition, set):
                assert len(condition) == 1
                condition = list(condition)[0]
            condition = frozenset({self.parent.get_by_label(l)
                                   for l in condition})
            self.twoway_conditions.add(condition)

        def check_can_reach_other(self, other=None, extra_satisfaction=None):
            # check reachability with backtracking, but slow every time
            nodes = {self}
            if other and other in nodes:
                return True
            done_nodes = set()
            edges = set()
            done_edges = set()
            if self.guaranteed is not None:
                satisfaction = set(self.guaranteed)
            else:
                satisfaction = {self}
            extra_satisfaction = extra_satisfaction or set()
            if not hasattr(self, '_reachable_cache'):
                self._reachable_cache = {}
            if extra_satisfaction <= satisfaction:
                cache_key = other
            else:
                cache_key = None
            if cache_key and cache_key in self._reachable_cache:
                return self._reachable_cache[other]
            satisfaction |= extra_satisfaction
            result = None
            while True:
                for n in nodes - done_nodes:
                    edges |= n.edges
                done_nodes |= nodes
                for n in (nodes-satisfaction) & self.parent.conditional_nodes:
                    if other and n.check_can_reach_other(
                            other, extra_satisfaction=satisfaction):
                        result = True
                        break
                    if n.check_can_reach_other(
                            self, extra_satisfaction=satisfaction):
                        satisfaction.add(n)
                if result is not None:
                    break
                for e in edges - done_edges:
                    if e.is_satisfied_by(satisfaction):
                        if e.destination is other:
                            result = True
                            break
                        nodes.add(e.destination)
                        done_edges.add(e)
                if result is not None:
                    break
                if not nodes - done_nodes:
                    break

            if result is None:
                if other:
                    result = other in done_nodes
                else:
                    result = nodes

            if cache_key:
                self._reachable_cache[cache_key] = result
                return self.check_can_reach_other(cache_key)
            else:
                return result

        def get_free_travel_nodes(self):
            if self.is_interesting:
                return {self}
            reachable_nodes = {self}
            reachable_from_nodes = {self}
            edges = set()
            reverse_edges = set()
            done_reachable_nodes = set()
            done_reachable_from_nodes = set()
            done_nodes = set()
            done_edges = set()
            done_reverse_edges = set()
            while True:
                if reachable_nodes == done_reachable_nodes and \
                        reachable_from_nodes == done_reachable_from_nodes:
                    break

                for n in reachable_nodes - done_reachable_nodes:
                    edges |= n.edges
                done_reachable_nodes |= reachable_nodes

                for n in reachable_from_nodes - done_reachable_from_nodes:
                    reverse_edges |= n.reverse_edges
                done_reachable_from_nodes |= reachable_from_nodes

                for e in edges - done_edges:
                    if not (e.destination.is_interesting
                            or e.combined_conditions):
                        reachable_nodes.add(e.destination)
                done_edges |= edges

                for e in reverse_edges - done_reverse_edges:
                    if not (e.source.is_interesting
                            or e.combined_conditions):
                        reachable_from_nodes.add(e.source)
                done_reverse_edges |= reverse_edges

            if hasattr(self, '_free_travel_nodes'):
                free_travel_nodes = reachable_nodes & reachable_from_nodes
                assert self._free_travel_nodes == free_travel_nodes
            return reachable_nodes & reachable_from_nodes

        def get_equivalent_nodes(self):
            if self.is_interesting:
                return {self}
            if not hasattr(self, '_equivalent_nodes'):
                if self.guaranteed is None:
                    return self.free_travel_nodes
                assert self.guaranteed is not None
                for n in self.free_travel_nodes:
                    n._equivalent_nodes = self.free_travel_nodes
            reachable_nodes = set(self.equivalent_nodes)
            old_reachable_nodes = set(reachable_nodes)
            while True:
                edges = {e for n in reachable_nodes for e in n.edges
                         if e.destination.guaranteed is not None
                         and e.destination not in reachable_nodes
                         and not e.destination.is_interesting}
                update = False
                for e in edges:
                    dest = e.destination
                    if e.is_satisfied_by(e.source.equivalent_guaranteed):
                        reverse_edges = {e for e in dest.edges
                                         if e.destination in reachable_nodes}
                        for e2 in reverse_edges:
                            if e2.is_satisfied_by(dest.equivalent_guaranteed):
                                reachable_nodes |= dest.equivalent_nodes
                                update = True
                                break
                    if update:
                        break

                if not update:
                    break

            reachable_nodes = frozenset(reachable_nodes)
            if reachable_nodes != old_reachable_nodes:
                for n in reachable_nodes:
                    n._equivalent_nodes = reachable_nodes
                    if hasattr(n, '_equivalent_guaranteed'):
                        delattr(n, '_equivalent_guaranteed')
                self.get_equivalent_nodes()
            return reachable_nodes

        def get_guaranteed_reachable(self, no_recurse=None,
                                     extra_satisfaction=None,
                                     update_guaranteed=False):
            if not hasattr(self, '_guaranteed_reachable_cache'):
                self._guaranteed_reachable_cache = {}
            if no_recurse is None:
                no_recurse = set()
            else:
                no_recurse = set(no_recurse)
            if extra_satisfaction is None:
                extra_satisfaction = set()
            assert self.guaranteed is not None

            def get_satisfaction():
                return self.parent.conditional_nodes & (
                        self.guaranteed | extra_satisfaction)
                #if update_guaranteed or True:
                #    return self.parent.conditional_nodes & (
                #            self.guaranteed | extra_satisfaction)
                #else:
                #    return self.parent.conditional_nodes & (
                #            self.equivalent_guaranteed | extra_satisfaction)
            reverse_satisfaction = frozenset(self.parent.conditional_nodes &
                                             extra_satisfaction)
            original_satisfaction = frozenset(get_satisfaction())
            satisfaction = set(original_satisfaction)
            # To use "interesting" no_recurse for cache key,
            # you MUST not recurse on uninteresting nodes
            cache_key = (frozenset(satisfaction),
                         frozenset(
                             (no_recurse | {self}) &
                             self.parent.conditional_nodes))

            #print(self, update_guaranteed, cache_key)
            if self in no_recurse and \
                    cache_key not in self._guaranteed_reachable_cache:
                raise Exception('Cannot self-recurse!')
            if cache_key in self._guaranteed_reachable_cache:
                return self._guaranteed_reachable_cache[cache_key]

            no_recurse.add(self)

            reachable_nodes = {self}
            for n in reachable_nodes:
                assert n.guaranteed is not None
            reachable_from_nodes = {self}
            if not update_guaranteed:
                reachable_nodes |= {n for n in self.equivalent_nodes
                                    if n.rank is not None}
            else:
                reachable_nodes |= {n for n in self.free_travel_nodes
                                    if n.rank is not None}
            reachable_from_nodes |= reachable_nodes
            edges = {e for n in reachable_nodes for e in n.edges}
            reverse_edges = {e for n in reachable_from_nodes
                             for e in n.reverse_edges}
            done_reachable_nodes = set(reachable_nodes)
            done_reachable_from_nodes = set(reachable_from_nodes)
            done_edges = {e for n in reachable_nodes for e in n.edges
                          if e.destination in reachable_nodes and
                          not e.combined_conditions}
            done_reverse_edges = set(done_edges)
            complete_done_edges = set(done_edges)

            for key, value in self._guaranteed_reachable_cache.items():
                ck_satisfaction, ck_no_recurse = key
                if ck_satisfaction <= satisfaction:
                    cache_rn, cache_rfn = value
                    reachable_nodes |= cache_rn
                    reachable_from_nodes |= cache_rfn

            if update_guaranteed and self is self.parent.root:
                assert reachable_nodes == {self}

            conditional_edges = {e for e in self.parent.all_edges
                                 if e.true_condition}
            guaranteed_tracker = {n: n.guaranteed for n in reachable_nodes}
            def invalidate_guaranteed(n):
                done_edges.difference_update(n.edges)
                done_reverse_edges.difference_update(n.edges)
                #for e in conditional_edges & done_edges:
                #    if n in e.full_true_condition:
                #        done_edges.remove(e)
                done_reachable_nodes.discard(n)
                done_reachable_from_nodes.discard(n)
                #if n in reachable_from_nodes - {self}:
                #    reachable_from_nodes.remove(n)
                guaranteed_tracker[n] = n.guaranteed

            def propagate_guaranteed(edge, override_fg):
                #print('PROPAGATE', edge)
                propagate_edges = {edge} | edge.destination.edges
                propagated_edges = set()
                valid_edges = complete_done_edges | {edge}
                counter = 0
                propagated = set()
                while True:
                    for e in (propagate_edges&valid_edges)-propagated_edges:
                        #print(' ', e)
                        dest = e.destination
                        assert dest.full_guaranteed is not None
                        assert dest.guaranteed is not None
                        dest.simplify_full_guaranteed()
                        for g in dest.full_guaranteed:
                            assert not g - dest.parent.conditional_nodes
                        old_guaranteed = (set(dest.full_guaranteed),
                                          frozenset(dest.guaranteed))
                        if e is edge:
                            full_guaranteed = override_fg
                        else:
                            full_guaranteed = {frozenset(
                                #g | e.full_true_condition | {dest}
                                g | e.true_condition | {dest}
                                | e.source.guaranteed)
                                for g in e.source.full_guaranteed}
                        #if '1b5-001' in str(full_guaranteed):
                        #    import pdb; pdb.set_trace()
                        dest.full_guaranteed |= full_guaranteed
                        temp = set(dest.full_guaranteed)
                        dest.guaranteed = dest.guaranteed & \
                                frozenset.intersection(
                                        *full_guaranteed)
                        dest.simplify_full_guaranteed()
                        if old_guaranteed != (dest.full_guaranteed,
                                              dest.guaranteed):
                            propagate_edges |= dest.edges
                            #propagated_edges -= dest.edges
                            #propagated_edges = set()
                            propagated.add(dest)
                    if propagated_edges >= propagate_edges:
                        break
                    propagated_edges |= propagate_edges

                    '''
                    to_propagate = propagate_nodes - propagated_nodes
                    if not to_propagate:
                        break
                    propagated_nodes |= propagate_nodes
                    for dest in to_propagate:
                        if dest.full_guaranteed is not None:
                            assert dest.guaranteed is not None
                            dest.simplify_full_guaranteed()
                            old_guaranteed = set(dest.full_guaranteed)
                            if dest.label == 'b':
                                print(dest.full_guaranteed)
                            dest.full_guaranteed |= full_guaranteed
                            dest.guaranteed = dest.guaranteed & \
                                    frozenset.intersection(
                                            *full_guaranteed)
                        else:
                            assert dest.guaranteed is None
                            assert dest is source
                            old_guaranteed = None
                            dest.full_guaranteed = full_guaranteed
                            dest.guaranteed = frozenset.intersection(
                                    *full_guaranteed)

                        #guaranteed_tracker[dest] = dest.guaranteed
                        dest.simplify_full_guaranteed()
                        if dest.full_guaranteed != old_guaranteed:
                            #import pdb; pdb.set_trace()
                            #if old_guaranteed is None:
                            #    invalidate_guaranteed(dest)
                            #invalidate_guaranteed(dest)
                            if dest not in reachable_nodes:
                                invalidate_guaranteed(dest)
                            #done_edges.difference_update(dest.edges)
                            #if dest not in reachable_from_nodes:
                            #    invalidate_guaranteed(dest)
                            #if dest is self.parent.root:
                            #    invalidate_guaranteed(dest)
                            for e in dest.edges & valid_edges:
                                propagate_nodes.add(e.destination)
                        if dest.full_guaranteed != old_guaranteed:
                            changed = True
                        if dest.label == 'b':
                            print(dest.full_guaranteed)
                        print(self, counter, source, dest)
                        #print(source, dest)
                    #if source is self.parent.root:
                    #    invalidate_guaranteed(source)
                    #    break
                if changed:
                    invalidate_guaranteed(source)
                assert source.full_guaranteed is not None
                assert source.guaranteed is not None
                '''

                return propagated

            satisfaction |= (reachable_nodes &
                             reachable_from_nodes &
                             self.parent.conditional_nodes)
            counter = 0
            complete_done_edges |= set(done_edges)
            while True:
                counter += 1
                undone_reachable_nodes = reachable_nodes - done_reachable_nodes
                undone_reachable_from_nodes = (reachable_from_nodes -
                                               done_reachable_from_nodes)
                for n in undone_reachable_nodes:
                    edges |= n.edges
                for n in undone_reachable_from_nodes:
                    reverse_edges |= n.reverse_edges
                done_reachable_nodes |= undone_reachable_nodes
                done_reachable_from_nodes |= undone_reachable_from_nodes

                new_satisfaction = set.intersection(
                        reachable_nodes, reachable_from_nodes,
                        self.parent.conditional_nodes)
                if new_satisfaction:
                    satisfaction |= new_satisfaction

                propagated = False
                if update_guaranteed:
                    edge_iterator = sorted(edges - done_edges)
                else:
                    edge_iterator = edges - done_edges
                #for e in edge_iterator:
                for e in sorted(edge_iterator, key=lambda x: x.source.label, reverse=True):
                    edge_result = e.is_full_satisfied_by(
                            satisfaction, strict=len(no_recurse)>1)
                    #if edge_result and edge_result is not True:
                    #    print(e, edge_result)
                    if edge_result is not False:
                        dest = e.destination
                        #print(e)
                        if update_guaranteed:
                            if edge_result is True:
                                full_guaranteed = {frozenset(
                                    #g | e.full_true_condition | {dest}
                                    g | e.true_condition | {dest}
                                    | e.source.guaranteed)
                                    for g in e.source.full_guaranteed}
                            else:
                                full_guaranteed = edge_result

                            if dest.full_guaranteed is None:
                                assert dest.guaranteed is None
                                dest.full_guaranteed = full_guaranteed
                                dest.guaranteed = frozenset.intersection(
                                        *full_guaranteed)
                            assert dest.guaranteed is not None
                            #print(e)
                            propagated = propagate_guaranteed(e, full_guaranteed) or propagated
                            '''
                            if dest.full_guaranteed is None:
                                dest.full_guaranteed = full_guaranteed
                            else:
                                dest.full_guaranteed |= full_guaranteed
                            if dest.guaranteed is not None:
                                dest.guaranteed = dest.guaranteed & \
                                        frozenset.intersection(
                                                *full_guaranteed)
                            else:
                                dest.guaranteed = frozenset.intersection(
                                        *full_guaranteed)
                            dest.simplify_full_guaranteed()
                            if old_guaranteed and dest.full_guaranteed != old_guaranteed:
                                import pdb; pdb.set_trace()
                                invalidate_guaranteed(dest)
                            print(self, counter, dest)
                            '''

                        if self is self.parent.root:
                            assert dest.guaranteed is not None
                        reachable_nodes.add(dest)
                        done_edges.add(e)
                        done_edges = {e2 for e2 in done_edges if dest not in e2.true_condition}
                        if edge_result is True:
                            complete_done_edges.add(e)

                #assert complete_done_edges >= done_edges
                if update_guaranteed:
                    for n in guaranteed_tracker:
                        if n.guaranteed != guaranteed_tracker[n]:
                            invalidate_guaranteed(n)

                    if get_satisfaction() != original_satisfaction:
                        return self.get_guaranteed_reachable(
                                no_recurse-{self}, extra_satisfaction,
                                update_guaranteed=update_guaranteed)

                edge_iterator = {e for e in reverse_edges - done_reverse_edges
                                 if e.source.guaranteed is not None
                                 or e.true_condition <= reverse_satisfaction}
                if edge_iterator:
                    for e in edge_iterator:
                        if e.source.guaranteed is not None:
                            my_satisfaction = (reverse_satisfaction |
                                               e.source.guaranteed)
                        elif e.true_condition:
                            continue
                        else:
                            my_satisfaction = reverse_satisfaction
                        result = e.is_full_satisfied_by(my_satisfaction)
                        if result is not False:
                            reachable_from_nodes.add(e.source)
                    done_reverse_edges |= edge_iterator

                if propagated:
                    done_edges = {e for e in done_edges if not e.true_condition}
                    #for e in complete_done_edges - done_edges:
                    #    print('REPROP', e)
                    continue

                #if done_edges < complete_done_edges:
                #    for e in complete_done_edges - done_edges:
                #        print('INCOMPLETE', e)
                #    continue

                for n in reachable_nodes:
                    assert n.guaranteed is not None

                if reachable_from_nodes <= done_reachable_from_nodes and \
                        reachable_nodes <= done_reachable_nodes:
                    update = False
                    double_check_nodes = (((
                            reachable_nodes & self.parent.conditional_nodes)
                            - reachable_from_nodes)
                            - no_recurse)
                    for n in double_check_nodes:
                        if len(no_recurse) > 1:
                            break
                        assert n.guaranteed is not None
                        rfn, nrf = n.get_guaranteed_reachable(
                                no_recurse=no_recurse,
                                extra_satisfaction=reverse_satisfaction,
                                update_guaranteed=update_guaranteed)
                        if rfn & reachable_from_nodes:
                            reachable_from_nodes.add(n)
                        reachable_nodes |= rfn
                else:
                    continue

                if reachable_from_nodes <= done_reachable_from_nodes and \
                        reachable_nodes <= done_reachable_nodes:
                    break

            #if update_guaranteed and self is self.parent.root:
            #    assert self.by_label('z') in reachable_nodes
            result = (frozenset(reachable_nodes),
                      frozenset(reachable_from_nodes))
            if update_guaranteed:
                self._guaranteed_reachable_cache[cache_key] = result
            else:
                for n in self.equivalent_nodes:
                    if not hasattr(n, '_guaranteed_reachable_cache'):
                        n._guaranteed_reachable_cache = {}
                    n._guaranteed_reachable_cache[cache_key] = result
            return self.get_guaranteed_reachable(
                    no_recurse, extra_satisfaction,
                    update_guaranteed=update_guaranteed)

        def get_reduced_guaranteed_reachable(self, update_guaranteed=False):
            if not self.parent.reduce:
                return self.get_guaranteed_reachable(
                        update_guaranteed=update_guaranteed)
            if not hasattr(self.parent, 'reduced_graph'):
                self.parent.reduced_graph = self.parent.get_reduced_graph()
            rgraph = self.parent.reduced_graph
            rgraph.reachable_from_root

            if DEBUG:
                t1 = time()
                rfn, nrf = self.get_guaranteed_reachable(
                        update_guaranteed=update_guaranteed)
                t2 = time()

            counterpart = rgraph.node_mapping[self]
            rfx, xrf = counterpart.get_guaranteed_reachable(
                    update_guaranteed=update_guaranteed)

            if update_guaranteed:
                for rn in rgraph.reachable_from_root:
                    full_guaranteed = {
                            rgraph.remap_nodes(g) &
                            self.parent.conditional_nodes
                            for g in rn.full_guaranteed}
                    guaranteed = rgraph.remap_nodes(rn.guaranteed) \
                            | frozenset.intersection(*full_guaranteed)
                    for n in rgraph.node_mapping[rn]:
                        n.full_guaranteed = full_guaranteed
                        n.provisional_guaranteed = guaranteed

            rfx = rgraph.remap_nodes(rfx)
            xrf = rgraph.remap_nodes(xrf)

            if DEBUG:
                t3 = time()
                a = t2-t1
                b = t3-t2
                #print(round(b/a, 2), int(round(a*1000000)),
                #      int(round(b*1000000)))
                #print(self, update_guaranteed, id(rgraph))
                assert (rfx == rfn) and (xrf == nrf)
                if update_guaranteed:
                    for n in rfn:
                        try:
                            assert n.guaranteed <= n.provisional_guaranteed
                        except:
                            for e in sorted(self.parent.all_edges):
                                print(e)
                            exit(0)

            if update_guaranteed:
                for n in rfx:
                    n.guaranteed = None
            return rfx, xrf

        def double_check_can_reach_root(self):
            if self in self.parent.root_reachable_from:
                return True
            if not self.rooted:
                return False
            reverse_edges = set()
            base_satisfaction = self.parent.double_rooted
            for e in self.reverse_edges:
                if not e.source in self.parent.double_rooted:
                    continue
                if not e.is_satisfied_by(base_satisfaction |
                                         e.source.guaranteed):
                    continue
                reverse_edges.add(e)
            if not reverse_edges:
                return False
            multi_guaranteed = frozenset.intersection(
                    *{e.source.guaranteed for e in reverse_edges})
            for e in self.edges:
                if e.destination not in self.parent.root_reachable_from:
                    continue
                if e.is_satisfied_by(self.guaranteed | multi_guaranteed):
                    raise Exception('Never seen this happen.')
                    return True
            return False

        def get_shortest_path(self, other=None, extra_satisfaction=None,
                              avoid_nodes=None, avoid_edges=None):
            if other is None:
                return self.parent.root.get_shortest_path(
                        other=self, extra_satisfaction=extra_satisfaction,
                        avoid_nodes=avoid_nodes, avoid_edges=avoid_edges)
            if self is other:
                return []
            if not self.rooted and other.rooted:
                raise Exception('Can only calculate paths of rooted nodes.')

            if isinstance(avoid_nodes, Graph.Node):
                avoid_nodes = frozenset({avoid_nodes})
            elif isinstance(avoid_nodes, set) and \
                    not isinstance(avoid_nodes, frozenset):
                avoid_nodes = frozenset(avoid_nodes)
            elif not avoid_nodes:
                avoid_nodes = frozenset()

            if isinstance(avoid_edges, Graph.Node.Edge):
                avoid_edges = frozenset({avoid_edges})
            elif not avoid_edges:
                avoid_edges = frozenset()

            if extra_satisfaction is None:
                extra_satisfaction = set()
            if self.guaranteed is not None:
                satisfaction = self.parent.conditional_nodes & (
                        self.guaranteed | extra_satisfaction)
            else:
                satisfaction = self.parent.conditional_nodes & \
                        extra_satisfaction

            rfn, nrf = self.get_reduced_guaranteed_reachable()
            if other not in rfn:
                return None

            # fast but fails against double one-way conditions?
            nodes = {self}
            done_nodes = set()
            edges = set()
            done_edges = set(avoid_edges)

            rank = 0
            rank_dict = {}
            while True:
                for n in nodes - done_nodes:
                    assert n not in rank_dict
                    rank_dict[n] = rank
                    edges |= n.edges
                if other in nodes:
                    break
                rank += 1
                done_nodes |= nodes
                for e in edges - done_edges:
                    if e.destination in avoid_nodes:
                        continue
                    if e.is_satisfied_by(satisfaction | done_nodes):
                        nodes.add(e.destination)
                        done_edges.add(e)
                if not nodes - done_nodes:
                    break

            if other not in nodes:
                return None

            def shortest_recurse(n):
                if n is self:
                    return []
                reverse_edges = {e for e in n.reverse_edges
                                 if e.source in rank_dict
                                 and e not in avoid_edges
                                 and e.source not in avoid_nodes
                                 and rank_dict[n] > rank_dict[e.source]}
                paths = [(e, shortest_recurse(e.source))
                         for e in reverse_edges]
                e, shortest = min(paths, key=lambda x: (len(x[1]), x))
                return shortest + [e]

            return shortest_recurse(other)

        def verify_required(self):
            if not self.required_nodes:
                return
            if not any(e.generated for e in self.double_edges):
                return
            orphaned = set()
            for e in self.edges:
                orphaned |= e.check_is_bridge()
            for r in sorted(self.required_nodes):
                if r not in self.parent.double_rooted:
                    assert r in self.parent.initial_unconnected or \
                            r.label in self.parent.preset_connections.keys()
                    raise DoorRouterException(f'{self} requires {r}.')
                if r in orphaned:
                    raise DoorRouterException(f'{self} requires {r}.')

        def verify_bridge(self):
            # TODO: Try reversing "bridge" exits?
            if not self.force_bridge:
                return
            if not self.rooted:
                return
            if self.parent.config['lazy_complex_nodes']:
                for other in self.force_bridge:
                    if self.force_bridge.rank is None or \
                            self.rank <= self.force_bridge.rank:
                        raise DoorRouterException(
                            f'Node {self} reachable from wrong direction.')
                return
            bridge_edges = frozenset({e for e in self.reverse_edges
                                      if e.source in self.force_bridge})
            assert bridge_edges
            extra_satisfaction = self.parent.nodes - self.get_orphanable()
            if self.get_shortest_path(avoid_edges=bridge_edges):
                raise DoorRouterException(
                    f'Node {self} reachable from wrong direction.')
            return

        def verify_guarantee(self):
            if not self.guarantee_nodes:
                return
            if not self.rooted:
                return
            if self.guarantee_nodes - self.guaranteed:
                raise DoorRouterException(
                    f'Node {self} reachable without guaranteed nodes.')
            return

        def verify(self):
            self.verify_required()
            self.verify_bridge()
            self.verify_guarantee()

    def __init__(self, filename=None, preset_connections=None,
                 strict_validator=None, lenient_validator=None,
                 testing=False, do_reduce=None, parent=None):
        self.testing = testing
        self.parent = parent
        if do_reduce is not None:
            self.reduce = do_reduce
        else:
            self.reduce = REDUCE and not self.parent
        if filename is None:
            filename = DEFAULT_CONFIG_FILENAME
        with open(filename) as f:
            self.config = yaml.load(f.read(), Loader=yaml.SafeLoader)
        self.config['config_filename'] = filename
        with open(DEFAULT_CONFIG_FILENAME) as f:
            defaults = yaml.load(f.read(), Loader=yaml.SafeLoader)
        for key in defaults:
            if key not in self.config:
                self.config[key] = defaults[key]
                print(f'Using default value {defaults[key]} for "{key}".')
        self.strict_validator = strict_validator
        self.lenient_validator = lenient_validator

        if preset_connections is None:
            preset_connections = {}
        self.preset_connections = preset_connections
        if 'seed' in self.config:
            self.seed = self.config['seed']
        elif self.parent:
            self.seed = (-abs(self.parent.seed)) - 1
        elif self.testing:
            self.seed = 0
        else:
            self.seed = random.randint(0, 9999999999)

        self.PREINITIALIZE_ATTRS = set()
        self.PREINITIALIZE_ATTRS |= set(dir(self))
        if self.testing or self.parent:
            self.initialize_empty()
        else:
            self.initialize()

    @property
    def description(self):
        s = ''
        s += 'Maze Generation Settings:\n'
        s += f'  seed:{"":15} {self.seed}\n'
        for key, value in self.config.items():
            if key == 'seed':
                continue
            key = f'{key}:'
            s += f'  {key:20} {value}\n'
        if self.num_loops > 0:
            s += f'\nCharacteristics:\n'
            key = 'longest path:'
            try:
                value = max(n.rank for n in self.nodes if n.rank is not None)
            except ValueError:
                value = -1
            s += f'  {key:20} {value}\n'
            if self.goal_reached and (self.root_reachable_from >=
                                      self.reachable_from_root):
                if not hasattr(self, 'solutions'):
                    self.generate_solutions()
                key = 'longest win path:'
                value = self.solutions[-1][1][-1].destination.rank
                s += f'  {key:20} {value}\n'
                required_nodes = set()
                for _, path in self.solutions:
                    required_nodes |= {p.destination for p in path}
                    required_nodes &= self.connectable
                key = 'required nodes:'
                value = len(required_nodes)
                s += f'  {key:20} {value}\n'
            key = 'total nodes:'
            value = len(self.connectable)
            s += f'  {key:20} {value}\n'
            key = 'generated edges:'
            value = len({e for e in self.all_edges if e.generated
                         and e.pair and e.source < e.destination})
            s += f'  {key:20} {value}\n'
            key = 'static edges:'
            value = len({e for e in self.all_edges if (not e.generated)
                         and e.pair and e.source < e.destination})
            s += f'  {key:20} {value}\n'
            key = 'trap doors:'
            value = len({e for e in self.all_edges if e.generated and
                         e.source is not e.destination and not e.soft_pairs})
            s += f'  {key:20} {value}\n'
            key = 'generation loops:'
            value = self.num_loops
            s += f'  {key:20} {value}\n'

        return s.strip()

    @property
    def description_problematic(self):
        s1 = self.description
        s2 = 'Problematic Nodes:\n'
        pnodes = sorted([(v, k) for (k, v) in self.problematic_nodes.items()
                         if v > 0], reverse=True)
        for count, node in pnodes[:10]:
            s2 += f'  {count:>4} {node}\n'
        return f'{s1}\n\n{s2}'.strip()

    def initialize_empty(self):
        self.root = None
        self.nodes = set()
        self.all_edges = set()
        self.conditionless_edges = set()
        self.connectable = set()
        self.conditional_nodes = set()
        self.guarantee_nodes = set()
        self.conditions = set()
        self.problematic_nodes = defaultdict(int)
        self.num_loops = -1
        self.definitions = {}

    def initialize(self):
        random.seed(self.seed)
        self.initialize_empty()

        nodes_filename = self.config['nodes_filename']
        try:
            lines = read_lines_nocomment(nodes_filename)
        except FileNotFoundError:
            from .tablereader import tblpath
            nodes_filename = path.join(tblpath, nodes_filename)
            lines = read_lines_nocomment(nodes_filename)

        for line in read_lines_nocomment(nodes_filename):
            if line.startswith('+'):
                self.Node(line[1:], self)
            else:
                self.connectable.add(self.Node(line, self))

        assert self.connectable
        self.unconnected = self.connectable - {
                self.get_by_label(l) for l in self.preset_connections.keys()}

        logic_filename = self.config['logic_filename']
        try:
            lines = read_lines_nocomment(logic_filename)
        except FileNotFoundError:
            from .tablereader import tblpath
            logic_filename = path.join(tblpath, logic_filename)
            lines = read_lines_nocomment(logic_filename)

        for line in lines:
            while '  ' in line:
                line = line.replace('  ', ' ')

            if line.startswith('.def'):
                _, definition_label, requirements = line.split(' ')
                assert definition_label not in self.definitions
                self.definitions[definition_label] = \
                        self.expand_requirements(requirements)
                continue

            if line.startswith('.start'):
                _, root_label = line.split(' ')
                self.set_root(self.get_by_label(root_label))
                continue

            if line.startswith('.goal'):
                _, requirements = line.split(' ')
                requirements = self.expand_requirements(requirements)
                self.set_goal(requirements)
                continue

            if line.startswith('.require'):
                _, node_label, requirements = line.split(' ')
                node = self.get_by_label(node_label)
                requirements = self.expand_requirements(requirements)
                for req in requirements:
                    for r in req:
                        node.required_nodes.add(self.get_by_label(r))
                continue

            if line.startswith('.guarantee'):
                _, node_label, requirements = line.split(' ')
                node = self.get_by_label(node_label)
                requirements = self.expand_requirements(requirements)
                for req in requirements:
                    for r in req:
                        node.add_guarantee(self.get_by_label(r))
                continue

            if line.startswith('.unreachable'):
                _, node_label = line.split(' ')
                node = self.get_by_label(node_label)
                self.nodes.remove(node)
                self.connectable.remove(node)
                self.unconnected.remove(node)
                continue

            assert not line.startswith('.')

            if ' ' in line:
                edge, conditions = line.split()
                conditions = self.expand_requirements(conditions)
            else:
                edge = line
                conditions = set()

            if '<' in edge:
                if '<=' in edge:
                    edge = '=>'.join(reversed(edge.split('<=')))
                elif '<<' in edge:
                    edge = '>>'.join(reversed(edge.split('<<')))
                else:
                    edge = '>'.join(reversed(edge.split('<')))
            assert '<' not in edge

            if len(conditions) == 0:
                conditions = {frozenset()}
            a, b = self.add_multiedge(edge, conditions)

        if self.preset_connections is not None:
            for alabel in self.preset_connections:
                a = self.get_by_label(alabel)
                for blabel, conditions in self.preset_connections[alabel]:
                    b = self.get_by_label(blabel)
                    if self.config['skip_complex_nodes'] >= 1 and (
                            a.guarantee_nodes or b.guarantee_nodes):
                        print(f'Warning: Fixed exit {a} -> {b} violates '
                              f'complex node policy. Removing this exit.')
                        self.unconnected |= {a, b}
                        continue
                    assert a in self.connectable
                    assert b in self.connectable
                    assert a not in self.unconnected
                    assert b not in self.unconnected
                    a.add_edge(b, conditions)

        assert self.unconnected <= self.connectable <= self.nodes
        num_nodes = int(round(self.config['map_size'] * len(self.unconnected)))
        reduced = self.necessary_nodes & self.unconnected
        too_complex = set()
        for n in sorted(self.unconnected):
            if (not n.guarantee_nodes) or \
                    random.random() > self.config['skip_complex_nodes']:
                continue
            else:
                too_complex.add(n)

        while True:
            candidates = sorted(self.unconnected - (too_complex| reduced))
            if not candidates:
                break
            chosen = random.choice(candidates)
            if chosen.guarantee_nodes and random.random() \
                    > self.config['map_size'] * self.config['map_strictness']:
                continue
            backup_reduced = set(reduced)
            reduced.add(chosen)
            while True:
                old_reduced = set(reduced)
                for n in old_reduced:
                    reduced |= n.local_conditional_nodes
                    for e in n.edges:
                        reduced.add(e.destination)
                    reduced |= n.required_nodes
                if reduced == old_reduced:
                    break
            if (reduced - backup_reduced) & too_complex:
                too_complex.add(chosen)
                reduced = backup_reduced
                continue
            if len(reduced & self.unconnected) >= num_nodes:
                break

        for n in reduced:
            assert n.required_nodes <= reduced
        assert self.necessary_nodes & self.unconnected == \
                self.necessary_nodes & reduced & self.unconnected
        self.unconnected = reduced & self.unconnected
        self.initial_unconnected = set(self.unconnected)

        assert self.unconnected <= self.connectable <= self.nodes
        del(self._property_cache)
        self.verify()
        self.commit()

    def reinitialize(self):
        random.seed(self.seed)
        self.seed = random.randint(0, 9999999999)
        post_initialize_attrs = set(dir(self)) - self.PREINITIALIZE_ATTRS
        for attr in post_initialize_attrs:
            delattr(self, attr)
        self.initialize()

    @property
    def rooted(self):
        return self.reachable_from_root

    @property
    def double_rooted(self):
        return self.reachable_from_root & self.root_reachable_from

        if hasattr(self, '_double_rooted'):
            return self._double_rooted
        self._double_rooted = self.reachable_from_root & \
                              self.root_reachable_from
        return self.double_rooted

    @property
    def reachable_from_root(self):
        if hasattr(self, '_reachable_from_root'):
            return self._reachable_from_root

        if DEBUG:
            print('FIND REACHABLE FROM ROOT')

        self.clear_node_guarantees()

        if self.reduce:
            self.reduced_graph = self.get_reduced_graph()

        rfr, rrf = self.root.get_reduced_guaranteed_reachable(
                update_guaranteed=True)
        self._reachable_from_root = rfr
        self._root_reachable_from = rrf

        unrooted = self.nodes - rfr
        for n in rfr:
            n._rooted = True
        for n in unrooted:
            n._rooted = False

        self.rerank_and_reguarantee()

        unranked = [n for n in rfr if n.rank is None]
        ranks = sorted(n.rank for n in rfr)
        nodes_by_rank_or_less = set()
        self.nodes_by_rank, self.nodes_by_rank_or_less = {}, {}
        for rank in ranks:
            self.nodes_by_rank[rank] = frozenset(
                    {n for n in rfr if n.rank == rank})
            nodes_by_rank_or_less |= self.nodes_by_rank[rank]
            self.nodes_by_rank_or_less[rank] = frozenset(nodes_by_rank_or_less)

        assert self._reachable_from_root
        assert self._root_reachable_from
        return self.reachable_from_root

    @property
    def root_reachable_from(self):
        if hasattr(self, '_root_reachable_from'):
            return self._root_reachable_from
        self.reachable_from_root
        return self.root_reachable_from

    @property
    def goal_reached(self):
        num_connected = len(self.initial_unconnected) - len(self.unconnected)
        if num_connected / len(self.initial_unconnected) < \
                self.config['map_strictness']:
            return False
        for condition in self.goal:
            if condition < self.double_rooted:
                return True
        return False

    @cached_property
    def goal_nodes(self):
        goal_nodes = set()
        for condition in self.goal:
            for n in condition:
                goal_nodes.add(n)
                goal_nodes |= n.required_nodes
        return goal_nodes

    @property
    def necessary_nodes(self):
        necessary = set(self.goal_nodes)
        necessary.add(self.root)
        while True:
            old_necessary = set(necessary)
            for n in old_necessary:
                if n in self.unconnected:
                    continue
                for e in n.reverse_edges:
                    necessary.add(e.source)
                    necessary |= e.source.local_conditional_nodes
                    if e.source in self.unconnected:
                        continue
            if necessary == old_necessary:
                break
        return necessary

    @property
    def interesting_nodes(self):
        return self.conditional_nodes | self.guarantee_nodes

    def get_by_label(self, label):
        for n in self.nodes:
            if n.label == label:
                return n

    def by_label(self, label):
        return self.get_by_label(label)

    def set_root(self, node):
        assert node in self.nodes
        self.root = node
        if not (self.testing or self.parent):
            assert self.root in self.connectable
        self.clear_rooted_cache()

    def set_goal(self, conditions):
        self.goal = {frozenset(self.get_by_label(l) for l in c)
                     for c in conditions}

    def clear_rooted_cache(self):
        cleared = False
        for attr in ('_reachable_from_root', '_root_reachable_from',
                     '_double_rooted', '_bridge_cache',
                     '_add_edge_options_cache', 'reduced_graph'):
            if hasattr(self, attr):
                if getattr(self, attr):
                    cleared = True
                delattr(self, attr)
        self._bridge_cache = {}
        for node in self.nodes:
            for attr in ('_reachable_cache',
                         '_guaranteed_reachable_cache',
                         '_free_travel_nodes', '_equivalent_nodes',
                         '_free_travel_guaranteed', '_equivalent_guaranteed'):
                if hasattr(node, attr):
                    delattr(node, attr)

        if DEBUG and cleared:
            print(self.num_loops, 'CLEAR ROOT')

    def clear_node_guarantees(self):
        for n in self.nodes:
            n.guaranteed = None
            n.full_guaranteed = None
            if hasattr(n, '_rooted'):
                delattr(n, '_rooted')
            if hasattr(n, 'provisional_guaranteed'):
                delattr(n, 'provisional_guaranteed')
            n.rank = None
        self.root.guaranteed = frozenset({self.root})
        self.root.full_guaranteed = {frozenset({self.root})}

    def expand_guarantee(self, guarantee, recursive=False):
        new_guarantee = frozenset({n2 for n1 in guarantee
                                   for n2 in n1.guaranteed})
        if recursive and new_guarantee != guarantee:
            return self.expand_guarantee(new_guarantee)
        return guarantee

    def expand_all_guarantees(self, nodes):
        counter = 0
        while True:
            updated = False
            for n in nodes:
                new_guaranteed = self.expand_guarantee(n.guaranteed)
                if new_guaranteed != n.guaranteed:
                    assert new_guaranteed >= n.guaranteed
                    updated = True
                    n.guaranteed = new_guaranteed
            if not updated:
                break
            counter += 1
        print('EXPAND', counter)

        while True:
            updated = False
            for n in nodes:
                new_full_guaranteed = {self.expand_guarantee(g)
                                       & self.conditional_nodes
                                       for g in n.full_guaranteed}
                if new_full_guaranteed != n.full_guaranteed:
                    updated = True
                    n.full_guaranteed = new_full_guaranteed
            if not updated:
                break

    def expand_requirements(self, requirements):
        assert isinstance(requirements, str)
        if requirements.startswith('suggest:'):
            return frozenset(set())
        if '&' in requirements:
            assert '|' not in requirements
            requirements = requirements.split('&')
            requirements = [self.definitions[r] if r in self.definitions
                            else {frozenset({r})} for r in requirements]
            while len(requirements) >= 2:
                a = requirements[0]
                b = requirements[1]
                requirements = requirements[2:]
                r = set()
                for aa in a:
                    for bb in b:
                        r.add(frozenset(aa | bb))
                requirements.append(r)
            assert len(requirements) == 1
            result = set(requirements[0])
        else:
            assert '&' not in requirements
            result = set()
            requirements = requirements.split('|')
            for r in requirements:
                if r in self.definitions:
                    defined = self.definitions[r]
                    assert isinstance(defined, set)
                    for r in defined:
                        assert isinstance(r, frozenset)
                        result.add(r)
                else:
                    result.add(frozenset({r}))
        for r in sorted(result):
            for compare in sorted(result):
                if r < compare and compare in result:
                    result.remove(compare)
        return result

    def split_edgestr(self, edgestr, operator):
        a, b = edgestr.split(operator)
        a = self.get_by_label(a)
        b = self.get_by_label(b)
        if a is None or b is None:
            raise Exception(f'{edgestr} contains unknown node.')
        return a, b

    def add_multiedge(self, edgestr, conditions):
        assert len(conditions) >= 1
        if '=>' in edgestr:
            a, b = self.split_edgestr(edgestr, '=>')
            a.add_edges(b, conditions)
            b.add_edges(a, conditions)
            b.force_bridge.add(a)
        elif '>>' in edgestr:
            a, b = self.split_edgestr(edgestr, '>>')
            a.required_nodes.add(b)
        elif '=' in edgestr:
            a, b = self.split_edgestr(edgestr, '=')
            if a is b:
                a.add_twoway_condition(conditions)
            else:
                a.add_edges(b, conditions)
                b.add_edges(a, conditions)
        elif '>' in edgestr:
            a, b = self.split_edgestr(edgestr, '>')
            a.add_edges(b, conditions)
        else:
            raise Exception(f'Invalid multiedge: {edgestr}')
        return (a, b)

    def rerank_and_reguarantee(self):
        # fast but fails against double one-way conditions
        nodes = {self.root}
        done_nodes = set()
        edges = set()
        done_edges = {e for e in self.all_edges
                      if not (e.source.rooted and e.destination.rooted)}

        for n in self.reachable_from_root:
            assert n.guaranteed or n.provisional_guaranteed
            if n.guaranteed is None:
                n.guaranteed = n.provisional_guaranteed

        self.root.guaranteed = frozenset({self.root})
        self.root.full_guaranteed = {frozenset({self.root})}
        #self.expand_all_guarantees(self.reachable_from_root)

        rank = 0
        while True:
            for n in nodes - done_nodes:
                assert n.guaranteed is not None
                n.rank = rank
                edges |= n.edges
            rank += 1
            done_nodes |= nodes
            for e in edges - done_edges:
                if e.is_satisfied_by(done_nodes):
                    nodes.add(e.destination)
                    new_guaranteed = e.destination.guaranteed & (
                            e.source.guaranteed | e.full_true_condition
                            | {e.destination})
                    success = True
                    if new_guaranteed != e.destination.guaranteed:
                        for n in e.true_condition:
                            assert n.guaranteed is not None
                            rfn, nrf = n.get_reduced_guaranteed_reachable()
                            if e.destination not in rfn:
                                success = False
                                break
                    if success:
                        done_edges.add(e)
                        e.destination.guaranteed = new_guaranteed
            if not nodes - done_nodes:
                break

        for n in sorted(self.reachable_from_root):
            if n.rank is None:
                print(n)
                for e in sorted(n.reverse_edges):
                    print(' ', e)
                    print(e.source.rank, e.true_condition <= done_nodes)
                print()

    def get_equivalence_groups(self):
        if hasattr(self, '_reachable_from_root'):
            nodes = set(self.reachable_from_root)
        else:
            nodes = set(self.nodes)

        equivalence_groups = set()
        while nodes:
            n = nodes.pop()
            group = n.equivalent_nodes
            assert group <= nodes | {n}
            nodes -= group
            equivalence_groups.add(group)

        for g1 in equivalence_groups:
            for g2 in equivalence_groups:
                if g1 is g2:
                    continue
                assert not (g1 & g2)

        return equivalence_groups

    def get_reduced_graph(self, minimal=None):
        assert REDUCE
        if minimal is None:
            #minimal = hasattr(self, '_reachable_from_root') and \
            #        not self.parent
            minimal = False

        rng_state = random.getstate()

        egs = self.get_equivalence_groups()
        eg_nodes = {n for eg in egs for n in eg}
        g = Graph(parent=self)
        g.node_mapping = {}
        leader_dict = {}
        sort_key = lambda n: (n.rank if n.rank is not None else -1, n)
        root = None
        for eg in egs:
            if self.root in eg:
                group_leader = self.root
            else:
                temp = eg & self.conditional_nodes
                if temp:
                    group_leader = min(temp, key=sort_key)
                else:
                    group_leader = min(eg, key=sort_key)

            leader_dict[eg] = group_leader
            n = g.Node(group_leader.label, g)
            g.node_mapping[n] = eg
            for n2 in eg:
                g.node_mapping[n2] = n
            if group_leader is self.root:
                root = n
        assert root is not None
        g.set_root(root)

        for e in self.all_edges:
            if not ({e.source, e.destination} <= eg_nodes):
                continue
            if e.destination in e.source.equivalent_nodes:
                continue
            if not (e.combined_conditions < eg_nodes):
                continue
            a = leader_dict[e.source.equivalent_nodes]
            b = leader_dict[e.destination.equivalent_nodes]
            if e.combined_conditions:
                true_condition = {leader_dict[n.equivalent_nodes].label
                                  for n in e.true_condition}
                false_condition = {leader_dict[n.equivalent_nodes].label
                                   for n in e.false_condition}
                condition = true_condition | {f'!{c}' for c in false_condition}
                if condition:
                    condition = '&'.join(condition)
            else:
                condition = None
            new_edge = g.add_edge(a.label, b.label,
                                  condition=condition, simplify=True,
                                  update_caches=False)

        g.clear_rooted_cache()
        assert not hasattr(g, '_reachable_from_root')
        if minimal:
            while True:
                g2 = g.get_reduced_graph(minimal=False)
                assert len(g2.nodes) <= len(g.nodes)
                assert len(g2.all_edges) <= len(g.all_edges)
                if len(g2.nodes) == len(g.nodes) and \
                        len(g2.all_edges) == len(g.all_edges):
                    break
                raise NotImplementedError('Need to update node mappings.')
                g = g2

        random.setstate(rng_state)

        return g

    def remap_nodes(self, nodes):
        if not nodes:
            return frozenset()
        if not hasattr(self, 'remapping_cache'):
            self.remapping_cache = {}
        if nodes in self.remapping_cache:
            return self.remapping_cache[nodes]
        parents = {n.parent is self for n in nodes}
        assert len(parents) == 1
        is_parent = parents.pop()
        self.remapping_cache[nodes] = \
                frozenset.union(*{self.node_mapping[n] for n in nodes})
        assert {n.parent is self != is_parent
                for n in self.remapping_cache[nodes]}
        return self.remap_nodes(nodes)

    def get_redundant_nodes(self):
        edges = []
        double_edges = []
        for n in self.nodes:
            if len(n.edges) >= 3 or len(n.reverse_edges) >= 3:
                continue
            if len(n.edges) != len(n.reverse_edges):
                continue
            if not (n.edges or n.reverse_edges):
                continue
            if len(n.edges) == 1:
                if list(n.edges)[0].destination is \
                        list(n.reverse_edges)[0].source:
                    continue
                edges.append((list(n.reverse_edges)[0], list(n.edges)[0]))
                continue
            for e in n.edges:
                if e.pair not in n.reverse_edges:
                    break
            else:
                assert len(n.edges) == len(n.reverse_edges) == 2
                a, b = sorted(n.edges)
                double_edges.append((b.pair, a))
                double_edges.append((a.pair, b))
        return double_edges + edges

    def get_no_return_nodes(self, allow_nodes):
        no_returns = set()
        nodes = sorted(self.reachable_from_root-self.root_reachable_from,
                       key=lambda n: (n.rank, n))
        if not nodes:
            return no_returns

        for n in nodes:
            rfn, nrf = n.get_reduced_guaranteed_reachable()
            others = rfn & allow_nodes
            if not others:
                raise DoorRouterException(
                        f'Unable to fix no return situation: {n}.')
            assert n in rfn
            no_returns |= rfn
        return no_returns

    def check_is_reachable_old(self, goal_node, avoid_nodes=None):
        if avoid_nodes is None:
            avoid_nodes = set()
        reachable = {self.root}
        done_nodes = set(avoid_nodes)
        done_edges = set(avoid_edges)
        test_edges = set()
        while True:
            test_nodes = reachable - done_nodes
            if not test_nodes:
                break
            for node in test_nodes:
                for edge in node.edges:
                    if edge.destination in done_nodes:
                        continue
                    test_edges.add(edge)
                done_nodes.add(node)
            for edge in test_edges - done_edges:
                if edge.is_satisfied_by(reachable):
                    if edge.destination is goal_node:
                        return True
                    reachable.add(edge.destination)
                    done_edges.add(edge)
        return False

    def get_add_edge_options(self):
        if hasattr(self, '_add_edge_options_cache'):
            return self._add_edge_options_cache
        options = []
        for o in sorted(self.unconnected):
            if not o.rooted:
                continue
            require_guarantee = o.required_nodes | o.guarantee_nodes
            if require_guarantee <= self.rooted:
                options.append(o)
        if not options:
            raise DoorRouterException('No connectable options.')

        if self.config['avoid_oneway_traps']:
            no_returns = self.get_no_return_nodes(allow_nodes=set(options))
            if no_returns:
                options = [o for o in options if o in no_returns]
                assert options
        else:
            no_returns = set()
        self._add_edge_options_cache = options, no_returns
        return self.get_add_edge_options()

    def commit(self, version=None):
        super().commit(version)
        for n in self.nodes:
            n.commit(version)

    def rollback(self, version=None):
        super().rollback(version)
        for n in self.nodes:
            n.rollback(version)

    def verify_no_return(self):
        if self.num_loops < 0:
            return
        self.get_add_edge_options()

    def verify_goal(self):
        if self.reachable_from_root - self.root_reachable_from:
            raise DoorRouterException(
                    'Graph contains points of no return.')
        for n in self.goal_nodes:
            if not n.rooted:
                raise DoorRouterException(
                    f'Unrooted goal node {n}.')
        if self.config['avoid_oneway_traps']:
            self.get_no_return_nodes(allow_nodes=set())
        return True

    def verify(self):
        for n in sorted(self.nodes, key=lambda n: n.label):
            try:
                n.verify()
            except DoorRouterException as error:
                self.problematic_nodes[n] += 1
                raise error
        self.verify_no_return()

    def add_edge(self, a, b, condition=None, procedural=False,
                 directed=True, simplify=False, update_caches=True):
        if isinstance(a, str):
            a = self.get_by_label(a)
        if isinstance(b, str):
            b = self.get_by_label(b)
        if condition is None:
            conditions = {frozenset()}
        elif isinstance(condition, frozenset):
            conditions = {condition}
        elif isinstance(condition, set):
            conditions = condition
        else:
            conditions = self.expand_requirements(condition)
        a.add_edges(b, conditions, procedural=procedural, simplify=simplify,
                    update_caches=update_caches)
        if not directed:
            b.add_edges(a, conditions,
                        procedural=procedural, simplify=simplify,
                        update_caches=update_caches)

    def procedural_add_edge(self, strict_candidates, lenient_candidates):
        options, no_returns = self.get_add_edge_options()

        a = random.choice(options)
        others = set(n for n in self.unconnected
                     if n.twoway_conditions == a.twoway_conditions)
        if random.random() > self.config['trap_doors']:
            others.remove(a)

        if a in strict_candidates:
            others &= strict_candidates[a]

        if a.rooted and random.random() < self.config['progression_speed']:
            temp = others & self.goal_nodes
            if temp:
                others = temp

        rate = self.config['oneway_cleanup_rate']
        denominator = len(self.unconnected | no_returns)
        rate *= (len(no_returns) / denominator)
        if no_returns and random.random() < rate:
            assert a in no_returns
            reachable, _ = a.get_reduced_guaranteed_reachable()
            temp = others & reachable
            if temp:
                others = temp

        temp = others - self.discourage_nodes[a]
        if temp:
            others = temp
        else:
            self.discourage_nodes[a] = set()

        if a in lenient_candidates:
            temp = others & lenient_candidates[a]
            if temp:
                others = temp

        if others:
            if a.rooted and self.config['linearity'] > 0:
                unranked = [n for n in others if n.rank is None]
                ranked = [n for n in others if n.rank is not None]
                ranked = sorted(ranked, key=lambda n: (abs(a.rank-n.rank),
                                                       n.sort_signature, n))
                unranked = sorted(unranked,
                                  key=lambda n: (n.sort_signature, n))
                others = unranked + ranked
                index = 1 - (random.random() ** (1-self.config['linearity']))
                max_index = len(others)-1
                b = others[int(round(index * max_index))]
            else:
                others = sorted(others)
                b = random.choice(others)
        else:
            b = a

        self.add_edge(a, b, directed=False, procedural=True, simplify=False)
        self.discourage_nodes[a].add(b)
        self.discourage_nodes[b].add(a)
        self.unconnected -= {a, b}
        log(f'ADD {a} {b}')

    def procedural_remove_edge(self):
        all_edges = {e for e in self.all_edges if e.generated}
        temp = all_edges - self.discourage_edges
        if temp:
            all_edges = temp
        else:
            self.discourage_edges = set()
        assert all_edges
        all_edges = sorted(all_edges)
        random.shuffle(all_edges)
        for e in all_edges:
            if not e.check_is_bridge():
                break
        self.discourage_edges.add(e)
        self.discourage_edges.add(e.pair)
        a, b = e.source, e.destination
        self.discourage_nodes[a].add(b)
        self.discourage_nodes[b].add(a)
        assert not self.unconnected & {a, b}
        old_rooted = self.rooted
        e.bidirectional_remove()
        self.unconnected |= {a, b}
        log(f'REMOVE {a} {b}')

    def handle_trap_doors(self):
        if self.config['trap_doors'] <= 0:
            return
        print('Adding trap doors...')
        self.verify()
        assert self.root_reachable_from >= self.reachable_from_root
        edges = [e for e in self.all_edges if e.source.rooted]
        trap_doors = [e for e in edges if e.source is e.destination]
        for e in sorted(trap_doors):
            if DEBUG:
                self.verify()
            rank = e.source.rank
            candidates = sorted([
                n for n in self.connectable
                if n.rank is not None and n.rank <= rank
                and n.twoway_conditions == e.source.twoway_conditions])
            candidates.remove(e.source)
            if not candidates:
                log('NO TRAP CANDIDATES', e)
                continue
            new_destination = random.choice(candidates)
            try:
                new_edge = e.source.add_edge(new_destination,
                                             procedural=True)
                log('TRAP', new_edge)
                self.verify()
                if self.reachable_from_root - self.root_reachable_from:
                    raise DoorRouterException(str(new_edge))
                e.remove()
            except DoorRouterException:
                new_edge.remove()
        self.verify()
        assert self.root_reachable_from >= self.reachable_from_root

    def generate_solutions(self, goal_nodes=None):
        print('Generating solution paths...')
        if not goal_nodes:
            goal_nodes = set(self.goal_nodes)
        paths = {}
        while True:
            for n in sorted(goal_nodes, key=lambda n: n.rank):
                if n in paths:
                    continue
                paths[n] = n.get_shortest_path(avoid_nodes=frozenset({
                    a for a in self.nodes
                    if a.rank is not None and a.rank > n.rank}))
                for e in paths[n]:
                    for c in e.true_condition:
                        goal_nodes.add(c)
            if goal_nodes == set(paths.keys()):
                break

        abridged_paths = []
        seen_edges = set()
        for n in sorted(goal_nodes, key=lambda n: (n.rank, n)):
            path = paths[n]
            seen_path = [p for p in path if p in seen_edges]
            if seen_path:
                start = seen_path[-1]
            else:
                start = path[0]
                assert start.source is self.root
            assert path.count(start) == 1
            assert len(path) == len(set(path))
            path = path[path.index(start):]
            seen_edges |= set(path)
            abridged_paths.append((n, path))

        self.solutions = abridged_paths
        return self.solutions

    def connect_everything(self):
        PROGRESS_BAR_LENGTH = 40
        PROGRESS_BAR_INTERVAL = (self.config['retry_limit'] //
                                 PROGRESS_BAR_LENGTH)

        strict_candidates = defaultdict(set)
        lenient_candidates = defaultdict(set)
        if self.strict_validator:
            for n1 in self.unconnected:
                for n2 in self.unconnected:
                    if n1 <= n2 and self.strict_validator(n1, n2):
                        strict_candidates[n1].add(n2)
                        strict_candidates[n2].add(n1)

        if self.lenient_validator:
            for n1 in self.unconnected:
                for n2 in self.unconnected:
                    if n1 <= n2 and self.lenient_validator(n1, n2):
                        lenient_candidates[n1].add(n2)
                        lenient_candidates[n2].add(n1)
            for n in self.unconnected:
                if n in strict_candidates and strict_candidates[n]:
                    lenient_candidates[n] = (lenient_candidates[n] &
                                             strict_candidates[n])

        self.discourage_nodes = defaultdict(set)
        self.discourage_edges = set()

        failures = 0
        start_time = time()
        initial_unconnected = set(self.unconnected)
        self.num_loops = 0
        previous_progress_bar = 0
        t1 = time()
        while True:
            self.num_loops += 1
            random.seed(f'{self.seed}-{self.num_loops}')

            t3 = time()
            self.priority_removals = None

            goal_reached = self.goal_reached
            if goal_reached:
                try:
                    self.verify_goal()
                    assert self.root_reachable_from >= self.reachable_from_root
                    break
                except DoorRouterException:
                    pass

            if self.num_loops // PROGRESS_BAR_INTERVAL > previous_progress_bar:
                previous_progress_bar += 1
                if goal_reached:
                    stdout.write('+')
                else:
                    stdout.write('.')
                stdout.flush()

            t2 = time()
            time_limit = self.config['time_limit']
            if t2 - t1 > time_limit:
                raise DoorRouterException(
                    f'Failed to build maze within {time_limit} seconds.\n'
                    f'Number of operations: {self.num_loops-1}')

            if self.num_loops > self.config['retry_limit_close'] or (
                    self.num_loops > self.config['retry_limit']
                    and not goal_reached):
                raise DoorRouterException(
                    f'Failed to build maze within {self.num_loops-1} '
                    f'operations.\nTime taken: {round(t2-t1,1)} seconds.')
            backup_unconnected = set(self.unconnected)

            if DEBUG:
                self.reachable_from_root
                self.verify()

            add_edge = False
            remove_edge = False
            if self.unconnected:
                assert self.unconnected & self.rooted
                if failures <= 1:
                    add_edge = True
                elif len(initial_unconnected) == len(self.unconnected):
                    add_edge = True
                elif random.random() > ((1/failures)**0.5):
                    add_edge = True
                else:
                    add_edge = False

            if add_edge:
                self.procedural_add_edge(strict_candidates,
                                         lenient_candidates)
            else:
                remove_edge = True

            if remove_edge:
                self.procedural_remove_edge()
                failures = 0

            unrootable = self.reachable_from_root - self.root_reachable_from
            report = f'{len(self.unconnected)}/' \
                    f'{len(unrootable)} {self.goal_reached}'
            try:
                if goal_reached and not self.goal_reached:
                    raise DoorRouterException(
                            f'Action would undo victory condition.')
                if not self.reachable_from_root & self.unconnected:
                    raise DoorRouterException(f'Orphaned root cluster.')
                self.verify()
                self.commit()
                failures = 0
            except DoorRouterException as error:
                self.unconnected = backup_unconnected
                self.rollback()
                report = f'{report} {error}'
                if DEBUG:
                    self.reachable_from_root
                    self.verify()
                failures += 1
            t4 = time()
            duration = int(round((t4-t3)*1000))
            report = f'{self.num_loops} {duration:>6}ms {report}'
            log(report)
        print()
        try:
            self.handle_trap_doors()
        except DoorRouterException as error:
            raise DoorRouterException(f'Trap door routing failure: {error}')

    def build_graph(self):
        attempts = 0
        while True:
            attempts += 1
            print(f'Maze generation attempt #{attempts}, seed {self.seed}...')
            print(f'Connecting {len(self.initial_unconnected)} nodes.')
            try:
                t1 = time()
                self.connect_everything()
                t2 = time()
                print(f'Completed maze on attempt #{attempts} after '
                      f'{self.num_loops} operations and {round(t2-t1,1)} '
                      f'seconds.')
                break
            except DoorRouterException as error:
                print()
                print(f'ERROR: {error}')
                if DEBUG:
                    print(self.description_problematic)
                sleep(1)
                self.reinitialize()

DoorRouter = Graph
