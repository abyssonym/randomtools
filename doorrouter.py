from .utils import cached_property, read_lines_nocomment, utilrandom as random
from collections import defaultdict
from copy import deepcopy
from functools import total_ordering
from hashlib import md5
from itertools import product
from sys import stdout
from time import time


DEBUG = False
LOGS = []
MAX_WAIT = 20
MAX_WAIT = 5
MAX_WAIT = 600


def log(line):
    LOGS.append(line)
    print(line)


class DoorRouterException(Exception):
    pass


class RollbackMixin:
    def commit(self):
        if not hasattr(self, '_rollback'):
            self._rollback = {}
        for attr in self.ROLLBACK_ATTRIBUTES:
            if not hasattr(self, attr):
                if attr in self._rollback:
                    del(self._rollback[attr])
                continue
            value = getattr(self, attr)
            value = type(value)(value)
            self._rollback[attr] = value

    def rollback(self):
        if not hasattr(self, '_rollback'):
            self._rollback = {}
        for attr in self.ROLLBACK_ATTRIBUTES:
            if attr not in self._rollback:
                if hasattr(self, attr):
                    delattr(self, attr)
                continue
            value = self._rollback[attr]
            value = type(value)(value)
            setattr(self, attr, value)


class Graph(RollbackMixin):
    ROLLBACK_ATTRIBUTES = {
        '_rooted', '_reachable_from_root', '_root_reachable_from',
        }

    @total_ordering
    class Node(RollbackMixin):
        ROLLBACK_ATTRIBUTES = {
            'edges', 'reverse_edges', '_subgroup',
            '_adjacent_nodes',
            '_rooted', '_reachable_from_root', '_root_reachable_from',
            '_interesting_nodes', '_reachable_by_interesting',
            }

        @total_ordering
        class Edge(RollbackMixin):
            ROLLBACK_ATTRIBUTES = {
                #'enabled',
                }
            GLOBAL_SORT_INDEX = 0

            def __init__(self, source, destination, condition, procedural):
                assert isinstance(source, Graph.Node)
                assert isinstance(destination, Graph.Node)
                assert isinstance(condition, frozenset)
                self.index = Graph.Node.Edge.GLOBAL_SORT_INDEX
                Graph.Node.Edge.GLOBAL_SORT_INDEX += 1
                self.true_condition = set()
                self.false_condition = set()
                self.source = source
                self.destination = destination
                self.procedural = procedural
                self.enabled = True
                self.source.edges.add(self)
                self.destination.reverse_edges.add(self)

                if condition:
                    assert all(isinstance(l, str) for l in condition)
                    for l in condition:
                        if l.startswith('!'):
                            node = self.source.parent.get_by_label(l[1:])
                            self.false_condition.add(node)
                        else:
                            node = self.source.parent.get_by_label(l)
                            self.true_condition.add(node)

                self.source.clear_reachable_cache()
                if self.source.rooted and not self.destination.rooted:
                    self.source.parent.clear_rooted_cache()
                self.source.clear_subgroup_cache()
                self.destination.clear_subgroup_cache()
                self.source.clear_adjacency_cache()
                self.destination.clear_adjacency_cache()

                self.commit()

            def __repr__(self):
                if not self.false_condition:
                    s = (f'{self.source}->{self.destination}: '
                         f'{sorted(self.true_condition)}')
                else:
                    s = (f'{self.source}->{self.destination}: '
                         f'{sorted(self.true_condition)} '
                         f'!{sorted(self.false_condition)}')
                if self.procedural:
                    s = f'{s}*'
                if not self.enabled:
                    s = f'{s} (DISABLED)'
                return s

            def __hash__(self):
                return hash(self.__repr__())

            def __eq__(self, other):
                return str(self) == str(other)

            def __lt__(self, other):
                return self.index < other.index

            @property
            def pair(self):
                candidates = {e for e in self.destination.edges if
                              e.destination is self.source and
                              e.true_condition == self.true_condition and
                              e.false_condition == self.false_condition and
                              e.procedural == self.procedural}
                assert len(candidates) <= 1
                if not candidates:
                    return None
                pair = sorted(candidates)[0]
                return pair

            def is_satisfied_by(self, nodes):
                if self.true_condition and self.true_condition - nodes:
                    return False
                if self.false_condition and self.false_condition & nodes:
                    return False
                return True

            def check_is_bridge(self):
                assert self.enabled
                before_nodes = self.source.parent.rooted
                self.enabled = False
                self.source.clear_reachable_cache()
                self.source.parent.clear_rooted_cache()
                after_nodes = self.source.parent.rooted
                self.enabled = True
                self.source.clear_reachable_cache()
                self.source.parent.clear_rooted_cache()
                if after_nodes - before_nodes:
                    return -1
                return before_nodes - after_nodes

            def bidirectional_check_is_bridge(self):
                assert self.enabled
                assert self.pair.enabled
                before_nodes = self.source.parent.rooted
                self.enabled = False
                self.pair.enabled = False
                self.source.clear_reachable_cache()
                self.pair.source.clear_reachable_cache()
                self.source.parent.clear_rooted_cache()
                after_nodes = self.source.parent.rooted
                self.enabled = True
                self.pair.enabled = True
                self.source.parent.clear_rooted_cache()
                self.source.clear_reachable_cache()
                self.pair.source.clear_reachable_cache()
                if after_nodes - before_nodes:
                    return -1
                return before_nodes - after_nodes

            def remove(self):
                self.source.edges.remove(self)
                self.destination.reverse_edges.remove(self)
                if self.source.rooted:
                    self.source.parent.clear_rooted_cache()
                self.source.clear_reachable_cache()
                self.source.clear_subgroup_cache()
                self.destination.clear_subgroup_cache()
                self.source.clear_adjacency_cache()
                self.destination.clear_adjacency_cache()

            def bidirectional_remove(self):
                self.remove()
                if self.pair is not None:
                    self.pair.remove()

        def __init__(self, label, parent):
            self.label = label
            self.parent = parent
            self._hash = hash(self.label)

            self.edges = set()
            self.reverse_edges = set()
            self.parent.nodes.add(self)

            self.required_nodes = set()
            self.approach_nodes = set()
            self.twoway_conditions = set()

        def __repr__(self):
            return self.label

        def __hash__(self):
            return self._hash

        def __eq__(self, other):
            assert isinstance(other, Graph.Node)
            if self is other:
                return True
            if self.label == other.label:
                raise Exception(f'Duplicate node: {self.label}')
            return False

        def __lt__(self, other):
            assert isinstance(other, Graph.Node)
            return self.label < other.label

        @property
        def double_edges(self):
            return self.edges | self.reverse_edges

        @property
        def rooted(self):
            if hasattr(self.parent, '_rooted'):
                return self._rooted
            self.parent.rooted
            return self.rooted

        @cached_property
        def is_procedural_node(self):
            return self in self.parent.procedural_nodes

        @property
        def interesting_nodes(self):
            if hasattr(self, '_interesting_nodes'):
                return self._interesting_nodes
            self._interesting_nodes = self.get_interesting_nodes()
            return self.interesting_nodes

        @property
        def reverse_nodes(self):
            return {e.source for e in self.reverse_edges} | {self}

        @property
        def adjacent_nodes(self):
            if hasattr(self, '_adjacent_nodes'):
                return self._adjacent_nodes
            self._adjacent_nodes = self.reverse_nodes | {e.destination
                                                         for e in self.edges}
            return self.adjacent_nodes

        @property
        def subgroup(self):
            if not self.is_procedural_node:
                return frozenset()
            if hasattr(self, '_subgroup'):
                return self._subgroup
            subgroup = {self}
            seen_nodes = set()
            while True:
                previous = set(subgroup)
                for n in subgroup - seen_nodes:
                    subgroup |= n.adjacent_nodes
                    seen_nodes.add(n)
                if subgroup == previous:
                    break
            self._subgroup = frozenset(subgroup & self.parent.procedural_nodes)
            assert self in self._subgroup
            for n in self.subgroup:
                n._subgroup = self.subgroup
            return self.subgroup

        def clear_subgroup_cache(self):
            if hasattr(self, '_subgroup'):
                for n in set(self._subgroup):
                    if hasattr(n, '_subgroup'):
                        del(n._subgroup)

        def get_reachable(self, nodes):
            old_nodes = set(nodes)
            nodes = frozenset(nodes & self.interesting_nodes)
            if not hasattr(self, '_reachable_by_interesting'):
                self._reachable_by_interesting = {}
            if nodes in self._reachable_by_interesting:
                return self._reachable_by_interesting[nodes]

            reachable = {self}
            for e in self.edges:
                if not e.enabled:
                    continue
                if e.is_satisfied_by(nodes):
                    reachable.add(e.destination)

            self._reachable_by_interesting[nodes] = reachable
            return self.get_reachable(nodes)

        def get_recursive_reachable(self, nodes=None):
            if nodes is None:
                nodes = set()
                reachable = {self}
            else:
                reachable = nodes
            reachable.add(self)
            while True:
                unchanged = set(reachable)
                for n in unchanged:
                    reachable |= n.get_reachable(reachable)
                if unchanged == reachable:
                    break
            return reachable

        def get_interesting_nodes(self):
            return ({c for e in self.edges for c in e.true_condition} |
                    {c for e in self.edges for c in e.false_condition})

        def clear_reachable_cache(self):
            if hasattr(self, '_interesting_nodes'):
                del(self._interesting_nodes)
            if hasattr(self, '_reachable_by_interesting'):
                del(self._reachable_by_interesting)

        def clear_adjacency_cache(self):
            if hasattr(self, '_adjacent_nodes'):
                del(self._adjacent_nodes)

        def add_edge(self, other, condition=None, procedural=False):
            if condition is None:
                condition = frozenset(set())
            else:
                assert isinstance(condition, frozenset)

            edge = self.Edge(self, other, condition, procedural=procedural)
            return edge

        def add_edges(self, other, conditions):
            for condition in conditions:
                self.add_edge(other, condition)
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
                    if edge1.false_condition != edge2.false_condition:
                        continue
                    if edge1.true_condition < edge2.true_condition:
                        self.edges.remove(edge2)

        def add_required(self, other):
            self.required_nodes.add(other)

        def add_approach(self, other):
            self.add_required(other)
            self.approach_nodes.add(other)

        def add_twoway_condition(self, condition):
            assert '!' not in condition
            if isinstance(condition, set):
                assert len(condition) == 1
                condition = list(condition)[0]
            condition = frozenset({self.parent.get_by_label(l)
                                   for l in condition})
            self.twoway_conditions.add(condition)

        def check_is_reachable(self, avoid_nodes=None):
            return self.parent.check_is_reachable(self, avoid_nodes)

        def commit(self):
            super().commit()
            assert self.edges is not self._rollback['edges']
            for e in self.edges:
                e.commit()

        def rollback(self):
            super().rollback()
            assert self.edges is not self._rollback['edges']
            for e in self.edges:
                e.rollback()

        def check_changed_subgroup(self):
            return self.subgroup != self.initial_subgroup

        def verify_twoway(self):
            if not self.twoway_conditions:
                return

            assert len(self.twoway_conditions) == 1
            for edge in self.reverse_edges:
                node = edge.source
                if self.twoway_conditions & node.twoway_conditions:
                    assert self.twoway_conditions == node.twoway_conditions
                    continue
                for condition in self.twoway_conditions:
                    if not (condition <= edge.true_condition):
                        raise DoorRouterException(
                            f'Invalid two-way restriction: {edge}')

        def verify_required(self):
            if not self.required_nodes:
                return
            if not self.check_changed_subgroup():
                return
            for r in self.required_nodes:
                if not r.rooted:
                    raise DoorRouterException(f'{self} requires {r}.')

        def verify_approach(self):
            if not self.approach_nodes:
                return
            if not self.check_changed_subgroup():
                return
            if not self.rooted:
                return
            reachable = self.check_is_reachable(
                    avoid_nodes=self.approach_nodes)
            if reachable:
                raise DoorRouterException(
                    f'Node {self} reachable from wrong direction.')

        def verify(self):
            if DEBUG:
                for e in self.edges:
                    assert e.source is self
                for e in self.reverse_edges:
                    assert e.destination is self

            self.verify_twoway()
            self.verify_required()
            self.verify_approach()

            if DEBUG and self.rooted:
                assert self in self.parent.rooted

    def __init__(self, node_labels, procedural_labels=None):
        if procedural_labels is None:
            procedural_labels = set()
        procedural_nodes = set()
        self.root = None
        self.goal = None
        self.nodes = set()
        for label in node_labels:
            node = self.Node(label, self)
            if label in procedural_labels:
                procedural_nodes.add(node)
        self.procedural_nodes = procedural_nodes
        self.minimum_coverage = 0.75
        assert self.procedural_nodes

    @property
    def rooted(self):
        if hasattr(self, '_rooted'):
            return self._rooted
        #if self.root is None:
        #    self._rooted = set()
        #else:
        #    self._rooted = frozenset(self.root.get_recursive_reachable())
        #    assert self.root in self._rooted
        self._rooted = self.reachable_from_root
        unrooted = self.nodes - self._rooted
        for n in self._rooted:
            n._rooted = True
        for n in unrooted:
            n._rooted = False
        if self.root:
            assert self.root in self._rooted
            assert self.root not in unrooted
            assert self.root.rooted
        return self.rooted

    @property
    def reachable_from_root(self):
        if hasattr(self, '_reachable_from_root'):
            return self._reachable_from_root
        if self.root is None:
            return frozenset()
        reachable_from_root = {self.root}
        done_nodes = set()
        done_edges = set()
        test_edges = set()
        while True:
            test_nodes = reachable_from_root - done_nodes
            if not test_nodes:
                break
            for node in test_nodes:
                for edge in node.edges:
                    test_edges.add(edge)
                done_nodes.add(node)
            for edge in test_edges - done_edges:
                if edge.is_satisfied_by(reachable_from_root):
                    assert edge.source in reachable_from_root
                    reachable_from_root.add(edge.destination)
                    done_edges.add(edge)
        self._reachable_from_root = reachable_from_root
        return self.reachable_from_root

    @property
    def root_reachable_from(self):
        # TODO: more robust propagation of edge conditions
        if hasattr(self, '_root_reachable_from'):
            return self._root_reachable_from
        root_reachable_from = {self.root}
        done_nodes = set()
        done_edges = set()
        test_edges = set()
        while True:
            test_nodes = root_reachable_from - done_nodes
            if not test_nodes:
                break
            for node in test_nodes:
                for edge in node.reverse_edges:
                    test_edges.add(edge)
                done_nodes.add(node)
            for edge in test_edges - done_edges:
                if edge.source.rooted and edge.is_satisfied_by(self.reachable_from_root):
                #if edge.is_satisfied_by(frozenset()):
                    assert edge.destination in root_reachable_from
                    root_reachable_from.add(edge.source)
                    done_edges.add(edge)
        self._root_reachable_from = root_reachable_from
        return self.root_reachable_from

    @property
    def goal_reached(self):
        if len(self.rooted) < self.minimum_coverage * len(self.nodes):
            return False
        for condition in self.goal:
            #if condition < (self.reachable_from_root &
            #                self.root_reachable_from):
            if condition < self.reachable_from_root:
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

    def get_by_label(self, label):
        for n in self.nodes:
            if n.label == label:
                return n

    def set_initial_subgroups(self):
        for n in self.nodes:
            n.initial_subgroup = n.subgroup

    def set_root(self, node):
        assert node in self.nodes
        self.root = node
        assert self.root in self.procedural_nodes
        self.clear_rooted_cache()
        assert self.root.rooted

    def set_goal(self, conditions):
        self.goal = {frozenset(self.get_by_label(l) for l in c)
                     for c in conditions}

    def clear_rooted_cache(self):
        if hasattr(self, '_rooted'):
            del(self._rooted)
        if hasattr(self, '_reachable_from_root'):
            del(self._reachable_from_root)
        if hasattr(self, '_root_reachable_from'):
            del(self._root_reachable_from)

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
            b.add_approach(a)
        elif '>>' in edgestr:
            a, b = self.split_edgestr(edgestr, '>>')
            a.add_edges(b, conditions)
            a.add_required(b)
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

    def check_is_reachable(self, goal_node, avoid_nodes=None):
        if avoid_nodes is None:
            avoid_nodes = set()

        nodes = {self.root}
        done_nodes = set()
        while True:
            new_nodes = {n for node in nodes - done_nodes
                         for n in node.get_reachable(nodes)} - nodes
            new_nodes -= avoid_nodes
            if not new_nodes:
                return False
            done_nodes |= nodes
            nodes |= new_nodes
            if goal_node in nodes:
                return True

    def get_cached_subgroup_reachability(self, key):
        CACHE_SIZE = 5000
        if not hasattr(self, '_subgroup_reachability_cache'):
            self._subgroup_reachability_cache = {}
        if key in self._subgroup_reachability_cache:
            return self._subgroup_reachability_cache[key]
        return None

    def cache_subgroup_reachability(self, key, reachability):
        CACHE_SIZE = 5000
        if not hasattr(self, '_subgroup_reachability_queue'):
            self._subgroup_reachability_queue = []
        self._subgroup_reachability_queue.append(key)
        if len(self._subgroup_reachability_cache) > CACHE_SIZE * 2:
            to_keep = self._subgroup_reachability_queue[-CACHE_SIZE:]
            self._subgroup_reachability_queue = to_keep
            to_keep = set(to_keep)
            for key in list(self._subgroup_reachability_cache):
                if key not in to_keep:
                    del(self._subgroup_reachability_cache[key])
        self._subgroup_reachability_cache[key] = reachability

    def get_subgroup_reachability(self, nodes):
        CACHING_ENABLED = False
        if DEBUG:
            assert len({n.subgroup for n in nodes}) == 1
            subgroup = sorted(nodes)[0].subgroup
            for n in nodes:
                try:
                    assert n.subgroup == subgroup
                    assert n.get_reachable(self.rooted) <= subgroup
                except:
                    exit(0)
                    import pdb; pdb.set_trace()
                n.clear_reachable_cache()
                n.clear_subgroup_cache()

        if CACHING_ENABLED:
            verify_cache = None
            key0 = nodes
            key1 = {e for n in nodes for e in n.double_edges}
            key2a = {c for e in key1 for c in e.true_condition}
            key2b = {c for e in key1 for c in e.false_condition}
            key2c = key2a | key2b
            key2 = {n for n in self.rooted if n in key2c}
            key = (frozenset(key0), frozenset(key1), frozenset(key2))
            result = self.get_cached_subgroup_reachability(key)
            if result is not None:
                if DEBUG and random.randint(1, 10) == 10:
                    verify_cache = result
                else:
                    return result

        reachability = {n: n.get_reachable(self.rooted) for n in nodes}
        changed = set(nodes)
        previous = None
        while True:
            old_changed = changed
            changed = set()
            updated = False
            for n1 in nodes:
                for n2 in old_changed & reachability[n1]:
                    new_nodes = reachability[n2] - reachability[n1]
                    if new_nodes:
                        reachability[n1] |= new_nodes
                        updated = True
                        changed.add(n1)
            if not updated:
                break

        if CACHING_ENABLED:
            if verify_cache is not None:
                assert reachability == verify_cache
                return reachability
            self.cache_subgroup_reachability(key, reachability)
        return reachability

    def reset_orphaned_clusters(self):
        reconnectable = set()
        for n in self.nodes - (self.reachable_from_root |
                               self.root_reachable_from):
            for e in set(n.double_edges):
                if e.procedural:
                    e.remove()
                    reconnectable.add(e.source)
                    reconnectable.add(e.destination)
            n.clear_subgroup_cache()
            n.clear_reachable_cache()
        return reconnectable

    def verify_subgroup_connectability(self, subgroup, connectable):
        reachability = self.get_subgroup_reachability(subgroup)
        for n in sorted(reachability):
            if not reachability[n] & connectable:
                print(f'X: {n} {len(connectable)} {sorted(reachability[n])}')
                return None
        return len(set(frozenset(r) for r in reachability.values()))

    def verify_all_connectability(self, connectable):
        if not self.reachable_from_root & connectable:
            raise DoorRouterException(f'Orphaned root cluster.')
        return
        if self.goal_reached:
            return
        subgroups = {n.subgroup
                     for n in self.procedural_nodes-self.reachable_from_root
                     if n.check_changed_subgroup()}
        unrooted = self.root.subgroup - self.root_reachable_from
        if unrooted:
            subgroups.add(unrooted)
        total_score = 0
        subgroup_sorter = lambda subgroup: ' '.join([str(g) for g in
                                                     sorted(subgroup)])
        if self.goal_reached:
            subgroups = {unrooted}
        for g in subgroups:
            for n in g:
                n.clear_subgroup_cache()
                n.clear_reachable_cache()
        for subgroup in sorted(subgroups, key=subgroup_sorter):
            score = self.verify_subgroup_connectability(subgroup,
                                                        connectable)
            if score is None:
                raise DoorRouterException(
                        f'Orphaned cluster: {sorted(subgroup)[0]}')
            total_score += score
        #if total_score > len(connectable & self.reachable_from_root):
        #    raise DoorRouterException(
        #            f'Insufficient rooted outlets for clusters.')

    def commit(self):
        super().commit()
        for n in self.nodes:
            n.commit()

    def rollback(self):
        super().rollback()
        for n in self.nodes:
            n.rollback()

    def verify(self):
        for n in self.nodes:
            n.verify()


class DoorRouter:
    def __init__(self, filename, node_labels, connectable_labels, root_label,
                 preset_connections=None,
                 strict_validator=None, lenient_validator=None):
        self.strict_validator = strict_validator
        self.lenient_validator = lenient_validator

        if preset_connections:
            procedural_labels = connectable_labels | preset_connections.keys()
        else:
            procedural_labels = connectable_labels
        assert root_label in procedural_labels
        self.graph = Graph(node_labels, procedural_labels)

        if preset_connections is not None:
            for alabel in preset_connections:
                a = self.graph.get_by_label(alabel)
                for blabel, conditions in preset_connections[alabel]:
                    b = self.graph.get_by_label(blabel)
                    a.add_edge(b, conditions)

        self.definitions = {}

        for line in read_lines_nocomment(filename):
            while '  ' in line:
                line = line.replace('  ', ' ')

            if line.startswith('.def'):
                _, definition_label, requirements = line.split(' ')
                assert definition_label not in self.definitions
                self.definitions[definition_label] = \
                        self.expand_requirements(requirements)
                continue

            if line.startswith('.goal'):
                _, requirements = line.split(' ')
                requirements = self.expand_requirements(requirements)
                self.graph.set_goal(requirements)
                continue

            if line.startswith('.guarantee'):
                _, node_label, requirements = line.split(' ')
                node = self.graph.get_by_label(node_label)
                requirements = self.expand_requirements(requirements)
                for req in requirements:
                    for r in req:
                        node.add_approach(self.graph.get_by_label(r))
                continue

            if line.startswith('.unreachable'):
                _, node_label = line.split(' ')
                node = self.graph.get_by_label(node_label)
                self.graph.nodes.remove(node)
                self.graph.procedural_nodes.remove(node)
                continue

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
            a, b = self.graph.add_multiedge(edge, conditions)

        self.graph.set_initial_subgroups()
        self.graph.set_root(self.graph.get_by_label(root_label))
        self.graph.verify()
        self.graph.commit()
        self.connectable = {n for n in self.graph.nodes
                            if n.label in connectable_labels} \
                                    & self.graph.procedural_nodes

    def expand_requirements(self, requirements):
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

    def prevalidate_twoway_conditions(self):
        all_twoways = set()
        for n in self.connectable:
            if n.twoway_conditions:
                assert len(n.twoway_conditions) == 1
                all_twoways.add(list(n.twoway_conditions)[0])

        for twoway in all_twoways:
            count = len([n for n in self.connectable
                         if n.twoway_conditions == {twoway}])
            assert count > 0
            assert count % 2 == 0

    def procedural_add_edge(self, strict_candidates, lenient_candidates):
        options = sorted(self.connectable)
        requirement = set()
        requiring = set()
        options = []
        for o in sorted(self.connectable):
            if o.required_nodes:
                requiring.add(o)
                requirement |= o.required_nodes
                if o.required_nodes <= self.graph.rooted:
                    options.append(o)
            else:
                options.append(o)

        if False and self.graph.goal_reached:
            options = [o for o in options
                       if o.rooted or o in self.graph.root_reachable_from]
        elif random.choice([True, True, True, False]):
            options = [o for o in options if o.rooted]
        if False and random.choice([True, False]):
            temp = [o for o in options if o.twoway_conditions]
            options = temp or options
        a = random.choice(options)
        others = set(n for n in self.connectable
                     if n.twoway_conditions == a.twoway_conditions)
        others.remove(a)
        if False and self.graph.goal_reached and random.choice([True, True, False]):
            others &= self.graph.rooted

        if a in strict_candidates:
            others &= strict_candidates[a]

        if a.rooted and random.choice([True, True, True, False]):
            temp = set()
            for n in self.graph.goal_nodes:
                if not n.rooted:
                    temp |= n.subgroup
            temp &= others
            others = temp or others
        if False and a.rooted and random.choice([True, self.graph.goal_reached, False]):
            temp = others - (self.graph.reachable_from_root &
                             self.graph.root_reachable_from)
            temp &= (self.graph.reachable_from_root |
                     self.graph.root_reachable_from)
            others = temp or others
        if False and a.rooted and random.choice([True, False]):
            temp = set()
            for n in requirement:
                temp |= n.subgroup
            temp &= others
            others = temp or others

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
            b = random.choice(sorted(others))
            others.remove(b)
        else:
            b = a

        #print(f'ADDING {a} {b}')
        edge_ab = a.add_edge(b, procedural=True)
        edge_ba = b.add_edge(a, procedural=True)
        self.discourage_nodes[a].add(b)
        self.discourage_nodes[b].add(a)

        new_connectable = self.connectable - {a, b}
        return new_connectable

    def procedural_remove_edge(self, removal_suggestion):
        twoways = []
        for c in removal_suggestion:
            if c.twoway_conditions not in twoways:
                twoways.append(c.twoway_conditions)
        all_edges = {e for n in self.graph.nodes
                     for e in n.double_edges if e.procedural
                     and e.source.twoway_conditions in twoways
                     }
                     #and (e.source.rooted or e.destination.rooted)}
        temp = all_edges - self.discourage_edges
        if temp:
            all_edges = temp
        else:
            self.discourage_edges = set()
        try:
            assert all_edges
        except:
            import pdb; pdb.set_trace()
        e = random.choice(sorted(all_edges))
        #if e.source.twoway_conditions not in twoways:
        #    continue
        self.discourage_edges.add(e)
        self.discourage_edges.add(e.pair)
        a, b = e.source, e.destination
        self.discourage_nodes[a].add(b)
        self.discourage_nodes[b].add(a)
        #assert a.rooted or b.rooted
        assert not self.connectable & {a, b}
        new_connectable = self.connectable | {a, b}
        #print(f'REMOVING {e}')
        old_rooted = self.graph.rooted
        e.bidirectional_remove()
        return new_connectable

    def connect_everything(self):
        # TODO: linearity controls
        # TODO: 1+ trap doors
        # TODO: RNG leaks
        # TODO: Count median cycles for successful run

        self.prevalidate_twoway_conditions()

        strict_candidates = defaultdict(set)
        lenient_candidates = defaultdict(set)
        if self.strict_validator:
            for n1 in self.connectable:
                for n2 in self.connectable:
                    if n1 < n2 and self.strict_validator(n1, n2):
                        strict_candidates[n1].add(n2)
                        strict_candidates[n2].add(n1)

        if self.lenient_validator:
            for n1 in self.connectable:
                for n2 in self.connectable:
                    if n1 < n2 and self.lenient_validator(n1, n2):
                        lenient_candidates[n1].add(n2)
                        lenient_candidates[n2].add(n1)
            for n in self.connectable:
                if n in strict_candidates and strict_candidates[n]:
                    lenient_candidates[n] = (lenient_candidates[n] &
                                             strict_candidates[n])

        self.discourage_nodes = defaultdict(set)
        self.discourage_edges = set()

        #assert len(connectable) % 2 == 0
        failures = 0
        start_time = time()
        assert self.connectable
        initial_connectable = set(self.connectable)
        random.random()
        while True:
            goal_reached = self.graph.goal_reached
            if goal_reached:
                self.connectable |= self.graph.reset_orphaned_clusters()
                if (self.graph.goal_nodes & self.graph.rooted) <= self.graph.root_reachable_from:
                    pass
                if self.graph.root_reachable_from == self.graph.reachable_from_root:
                    import pdb; pdb.set_trace()

            if time() - start_time > MAX_WAIT:
                break

            backup_connectable = set(self.connectable)
            if DEBUG:
                self.graph.verify()

            add_edge = False
            if self.connectable:
                assert self.connectable & self.graph.rooted
                if failures <= 1:
                    add_edge = True
                elif len(initial_connectable) == len(self.connectable):
                    add_edge = True
                elif random.random() > ((1/failures)**0.5):
                    add_edge = True
                else:
                    add_edge = False
                    removal_suggestion = self.connectable
            else:
                unrooted = self.graph.nodes - (self.graph.reachable_from_root &
                                               self.graph.root_reachable_from)
                if not unrooted:
                    break
                removal_suggestion = unrooted

            if add_edge:
                new_connectable = self.procedural_add_edge(strict_candidates,
                                                           lenient_candidates)
            else:
                new_connectable = \
                        self.procedural_remove_edge(removal_suggestion)
                failures = 0

            assert new_connectable != self.connectable
            assert new_connectable is not None

            try:
                if goal_reached and not self.graph.goal_reached:
                    raise DoorRouterException(
                            f'Action would undo victory condition.')
                if self.graph.goal_reached and (self.graph.goal_nodes & self.graph.rooted) <= self.graph.root_reachable_from:
                    pass
                self.graph.verify_all_connectability(new_connectable)
                self.graph.verify()
                self.graph.commit()
                failures = 0
                self.connectable = new_connectable
            except DoorRouterException as error:
                self.connectable = backup_connectable
                self.graph.rollback()
                unreachable = self.graph.procedural_nodes - self.graph.reachable_from_root
                unrootable = self.graph.procedural_nodes - self.graph.root_reachable_from
                report = f'{len(self.connectable)}/{len(unreachable)}/{len(unrootable)} {self.graph.goal_reached} {error}'
                print(report)
                if DEBUG:
                    self.graph.verify()
                failures += 1

        if stdout.isatty():
            import pdb; pdb.set_trace()
        else:
            exit(0)
