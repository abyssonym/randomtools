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
STRICT_GUARANTEE_CHECKS = False
MODULE_FILEPATH, _ = path.split(__file__)
DEFAULT_CONFIG_FILENAME = path.join(MODULE_FILEPATH, 'default.doorrouter.yaml')


def log(line):
    if DEBUG:
        line = line.strip()
        print(line)


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
            if value is not None:
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
            if value is not None:
                value = type(value)(value)
            setattr(self, attr, value)


class Graph(RollbackMixin):
    ROLLBACK_ATTRIBUTES = {
        'all_edges', 'conditionless_edges',
        '_reachable_from_root', '_root_reachable_from', '_double_rooted',
        '_avoid_reachable_cache', '_avoid_reachable_invalidated',
        '_bridge_cache',
        }

    @total_ordering
    class Node(RollbackMixin):
        ROLLBACK_ATTRIBUTES = {
            'edges', 'reverse_edges', 'rank', 'guaranteed', '_rooted',
            }

        @total_ordering
        class Edge(RollbackMixin):
            ROLLBACK_ATTRIBUTES = {}
            GLOBAL_SORT_INDEX = 0

            def __init__(self, source, destination, condition, procedural):
                assert isinstance(source, Graph.Node)
                assert isinstance(destination, Graph.Node)
                assert isinstance(condition, frozenset)
                self.index = Graph.Node.Edge.GLOBAL_SORT_INDEX
                Graph.Node.Edge.GLOBAL_SORT_INDEX += 1

                self.source = source
                self.destination = destination
                self.generated = procedural

                self.true_condition = set()
                self.false_condition = set()
                if condition:
                    assert all(isinstance(l, str) for l in condition)
                    for l in condition:
                        if l.startswith('!'):
                            requirements = \
                                self.source.parent.expand_requirements(l[1:])
                            assert len(requirements) == 1
                            for req in requirements:
                                for node in req:
                                    node = \
                                        self.source.parent.get_by_label(node)
                                    assert isinstance(node, Graph.Node)
                                    self.false_condition.add(node)
                        else:
                            node = self.source.parent.get_by_label(l)
                            self.true_condition.add(node)
                        assert node is not None
                assert self.__hash__() == self.signature.__hash__()

                self.enabled = True
                self.source.edges.add(self)
                self.destination.reverse_edges.add(self)
                self.source.parent.all_edges.add(self)
                if not self.combined_conditions:
                    self.source.parent.conditionless_edges.add(self)
                if self.source.rooted:
                    self.source.parent.clear_rooted_cache()
                self.source.parent.invalidate_node_reachability(
                    {self.source, self.destination})

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

            @cached_property
            def combined_conditions(self):
                return self.true_condition | self.false_condition

            def is_satisfied_by(self, nodes):
                if not self.enabled:
                    return False
                if self.true_condition and self.true_condition - nodes:
                    return False
                if self.false_condition and self.false_condition & nodes:
                    return False
                return True

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
                self.source.parent.invalidate_node_reachability(
                    {self.source, self.destination})
                rfr2, rrf2 = (self.source.parent.reachable_from_root,
                              self.source.parent.root_reachable_from)
                self.enabled = True
                self.source.parent.clear_rooted_cache()
                self.source.parent.invalidate_node_reachability(
                    {self.source, self.destination})
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
                self.source.parent.invalidate_node_reachability(
                    {self.source, self.destination})

            def bidirectional_remove(self):
                self.remove()
                if self.pair and self.pair is not self:
                    self.pair.remove()

        def __init__(self, label, parent):
            self.label = label
            self.parent = parent
            self._hash = hash(self.label)
            self.rank = None
            self.sort_signature = random.random()
            self.force_bridge = set()

            self.edges = set()
            self.reverse_edges = set()
            self.parent.nodes.add(self)

            self.required_nodes = set()
            self.guarantee_nodes = set()
            self.twoway_conditions = set()

            self.commit()

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
            return self.label < other.label

        @property
        def double_edges(self):
            return self.edges | self.reverse_edges

        @property
        def rooted(self):
            if hasattr(self, '_rooted'):
                return self._rooted
            self.parent.rooted
            return self.rooted

        @cached_property
        def is_connectable_node(self):
            return self in self.parent.connectable

        @cached_property
        def is_interesting(self):
            return self in self.parent.interesting_nodes

        @cached_property
        def interesting_nodes(self):
            return {c for e in self.edges for c in e.combined_conditions}

        @property
        def reverse_nodes(self):
            return {e.source for e in self.reverse_edges} | {self}

        @property
        def generated_edges(self):
            return {e for e in self.all_edges if e.generated}

        def add_edge(self, other, condition=None, procedural=False):
            if condition is None:
                condition = frozenset(set())
            else:
                assert isinstance(condition, frozenset)

            edge = self.Edge(self, other, condition, procedural=procedural)
            return edge

        def add_edges(self, other, conditions):
            for condition in sorted(conditions, key=lambda c: sorted(c)):
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
                    if edge1.false_condition >= edge2.false_condition and \
                            edge1.true_condition <= edge2.true_condition:
                        self.edges.remove(edge2)

        def get_orphanable_old(self):
            # Get orphans; does not account for edge conditions
            before_rooted = self.parent.rooted
            for e in self.edges:
                e.enabled = False
            after_rooted = self.parent.fast_get_reachable()
            for e in self.edges:
                e.enabled = True
            return before_rooted - after_rooted

        def get_orphanable_fast(self):
            before_rooted = self.parent.rooted - {self}
            after_rooted, after_edges = self.parent.get_avoid_reachable(
                    avoid_nodes=frozenset({self}))
            return before_rooted - after_rooted[max(after_rooted)]

        def get_orphanable_slow(self):
            return self.parent.rooted - self.parent.fast_get_reachable(
                    avoid_nodes=frozenset({self})) - {self}

        def get_orphanable(self):
            a = self.get_orphanable_fast()
            if DEBUG:
                b = self.get_orphanable_slow()
                assert a == b
            return a

        def add_guarantee(self, other):
            if self.parent.config['lazy_complex_nodes']:
                self.required_nodes.add(other)
            else:
                self.guarantee_nodes.add(other)

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

        def get_shortest_path(self, avoid_nodes=None, avoid_edges=None):
            if isinstance(avoid_edges, Graph.Node.Edge):
                avoid_edges = frozenset({avoid_edges})
            elif not avoid_edges:
                avoid_edges = frozenset()
            stage_nodes, stage_edges = \
                    self.parent.get_avoid_reachable(avoid_nodes=avoid_nodes,
                                                    avoid_edges=avoid_edges)
            for stage_number in sorted(stage_nodes):
                if self in stage_nodes[stage_number]:
                    break
            else:
                return None

            nodes_path = [self]
            edges_path = []
            i = stage_number
            while True:
                assert i >= 0
                if i == 0:
                    assert nodes_path[0] is self.parent.root
                    break

                j = i-2
                while True:
                    if i >= 2:
                        edges = stage_edges[i-1] - stage_edges[j]
                    else:
                        edges = stage_edges[i-1]
                    previous_nodes = stage_nodes[i-1]
                    candidates = [e for e in edges
                                  if e.destination is nodes_path[0]
                                  and e not in avoid_edges]
                    candidates = [e for e in candidates
                                  if e.is_satisfied_by(previous_nodes)]
                    if candidates:
                        break
                    j -= 1

                chosen = max(candidates)
                nodes_path.insert(0, chosen.source)
                edges_path.insert(0, chosen)
                i = j+1

            return edges_path

        def verify_required(self):
            if not self.required_nodes:
                return
            if not any(e.generated for e in self.double_edges):
                return
            orphaned = set()
            for e in self.edges:
                orphaned |= e.check_is_bridge()
            for r in self.required_nodes:
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
            if self.get_shortest_path(avoid_edges=bridge_edges):
                raise DoorRouterException(
                    f'Node {self} reachable from wrong direction.')
            return
            for e in self.edges:
                if not e.generated:
                    continue
                if not e.check_is_bridge():
                    raise DoorRouterException(
                        f'Node {self} reachable from wrong direction.')

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
            if DEBUG:
                for e in self.edges:
                    assert e.source is self
                for e in self.reverse_edges:
                    assert e.destination is self

            self.verify_required()
            self.verify_bridge()
            self.verify_guarantee()
            if DEBUG and self.rooted and self.guaranteed:
                for e in self.edges:
                    assert e.source.rooted
                    if not e.destination.rooted:
                        continue
                    if e.destination.rank > e.source.rank:
                        orphans = e.check_is_bridge()
                        for o in orphans:
                            assert o.guaranteed >= self.guaranteed
                if STRICT_GUARANTEE_CHECKS:
                    for o in self.get_orphanable():
                        assert o.guaranteed >= self.guaranteed

            if DEBUG and self.rooted:
                assert self in self.parent.rooted

    def __init__(self, filename, preset_connections=None,
                 strict_validator=None, lenient_validator=None):
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
        else:
            self.seed = random.randint(0, 9999999999)

        self.PREINITIALIZE_ATTRS = set()
        self.PREINITIALIZE_ATTRS |= set(dir(self))
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
            value = max(n.rank for n in self.nodes if n.rank is not None)
            s += f'  {key:20} {value}\n'
            if self.goal_reached and (self.reachable_from_root ==
                                      self.root_reachable_from):
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
            value = len({e for e in self.all_edges if e.generated
                         and e.pair is None and e.source is not e.destination})
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

    def initialize(self):
        random.seed(self.seed)

        self.root = None
        self.nodes = set()
        self.all_edges = set()
        self.conditionless_edges = set()
        self.connectable = set()
        self.problematic_nodes = defaultdict(int)
        self.num_loops = -1

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

        self.definitions = {}

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
                    reduced |= n.interesting_nodes
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

        for n in self.nodes:
            if hasattr(n, 'guaranteed'):
                del(n.guaranteed)
                n.rank = None
        self.nodes_by_rank_or_less = defaultdict(set)
        self.nodes_by_rank = defaultdict(set)
        self.root.guaranteed = set()
        nodes = {self.root}
        edges = set()
        done_nodes = set()
        done_edges = set()
        rank = 0
        while True:
            self.nodes_by_rank[rank] = frozenset(nodes - done_nodes)
            self.nodes_by_rank_or_less[rank] = frozenset(nodes)
            for n in self.nodes_by_rank[rank]:
                n.rank = rank
                edges |= n.edges
            rank += 1
            done_nodes |= nodes
            for e in edges - done_edges:
                if e.is_satisfied_by(done_nodes):
                    if hasattr(e.destination, 'guaranteed'):
                        e.destination.guaranteed &= e.true_condition
                    else:
                        e.destination.guaranteed = set(e.true_condition)
                    if e.destination.is_interesting:
                        e.destination.guaranteed.add(e.destination)
                    nodes.add(e.destination)
                    done_edges.add(e)
            if not nodes - done_nodes:
                break

        if DEBUG:
            assert nodes == self.fast_get_reachable()
        self._reachable_from_root = nodes
        unrooted = self.nodes - nodes
        for n in nodes:
            n._rooted = True
            assert n.rank is not None
        for n in unrooted:
            n._rooted = False
            n.rank = None

        nodes_with_guarantees = {n for n in nodes if n.guaranteed}
        assert self._reachable_from_root
        self.root_reachable_from
        while True:
            updated = False
            for n1 in set(nodes_with_guarantees):
                for n2 in list(n1.guaranteed):
                    if n2.guaranteed - n1.guaranteed:
                        n1.guaranteed |= n2.guaranteed
                        updated = True
                for e in n1.edges:
                    if e.destination.rooted and \
                            e.destination.rank > e.source.rank:
                        for o in e.check_is_bridge():
                            if n1.guaranteed - o.guaranteed:
                                o.guaranteed |= n1.guaranteed
                                updated = True
                                nodes_with_guarantees.add(o)
            if not updated:
                break

        if STRICT_GUARANTEE_CHECKS:
            for n1 in nodes_with_guarantees & self.interesting_nodes:
                for o in n1.get_orphanable():
                    if n1.guaranteed - o.guaranteed:
                        o.guaranteed |= n1.guaranteed

        return self.reachable_from_root

    @property
    def root_reachable_from(self):
        if hasattr(self, '_root_reachable_from'):
            return self._root_reachable_from
        self.reachable_from_root

        if DEBUG:
            print('FIND ROOT REACHABLE FROM')

        root_reachable_from = {self.root}
        done_nodes = set()
        done_edges = set()
        test_edges = set()
        counter = 0
        satisfaction_cache = {}
        while True:
            counter += 1
            test_nodes = root_reachable_from - done_nodes
            if not test_nodes:
                break
            for node in test_nodes:
                for edge in node.reverse_edges:
                    test_edges.add(edge)
                done_nodes.add(node)
            for edge in test_edges - done_edges:
                if not edge.source.rooted:
                    continue
                if edge.source.rank not in satisfaction_cache:
                    satisfaction_cache[edge.source.rank] = set(
                            self.nodes_by_rank_or_less[edge.source.rank-1]
                            & root_reachable_from)
                satisfaction = satisfaction_cache[edge.source.rank]
                if STRICT_GUARANTEE_CHECKS:
                    satisfaction = edge.source.guaranteed
                if edge.is_satisfied_by(satisfaction):
                    root_reachable_from.add(edge.source)
                    if edge.source.is_interesting:
                        for rank in sorted(satisfaction_cache):
                            if rank >= edge.source.rank:
                                del(satisfaction_cache[rank])
                    done_edges.add(edge)
        self._root_reachable_from = root_reachable_from
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
                    necessary |= e.source.interesting_nodes
                    if e.source in self.unconnected:
                        continue
            if necessary == old_necessary:
                break
        return necessary

    @cached_property
    def interesting_nodes(self):
        return {n for e in self.all_edges for n in e.combined_conditions}

    def get_by_label(self, label):
        for n in self.nodes:
            if n.label == label:
                return n

    def set_root(self, node):
        assert node in self.nodes
        self.root = node
        assert self.root in self.connectable
        self.clear_rooted_cache()
        assert self.root.rooted

    def set_goal(self, conditions):
        self.goal = {frozenset(self.get_by_label(l) for l in c)
                     for c in conditions}

    def clear_rooted_cache(self):
        cleared = False
        for attr in ('_reachable_from_root', '_root_reachable_from',
                     '_double_rooted', '_bridge_cache'):
            if hasattr(self, attr):
                if getattr(self, attr):
                    cleared = True
                delattr(self, attr)
        self._bridge_cache = {}
        if DEBUG and cleared:
            print(self.num_loops, 'CLEAR ROOT')

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
            a.add_edges(b, conditions)
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

    def fast_get_reachable(self, avoid_nodes=None):
        if avoid_nodes is None:
            avoid_nodes = set()
        done_nodes = set(avoid_nodes)
        nodes = {self.root}
        edges = set()
        done_edges = set()
        while True:
            for n in nodes - done_nodes:
                edges |= n.edges
            done_nodes |= nodes
            for e in edges - done_edges:
                if e.is_satisfied_by(done_nodes-avoid_nodes):
                    nodes.add(e.destination)
                    done_edges.add(e)
            if not nodes - done_nodes:
                break
        return nodes - avoid_nodes

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

    def get_avoid_reachable(self, avoid_nodes=None, avoid_edges=None):
        self.reachable_from_root
        assert hasattr(self, '_reachable_from_root')
        if avoid_nodes is None:
            avoid_nodes = frozenset()
        elif isinstance(avoid_nodes, Graph.Node):
            avoid_nodes = frozenset({avoid_nodes})
        if avoid_edges is None:
            avoid_edges = frozenset()
        elif isinstance(avoid_edges, Graph.Node.Edge):
            avoid_edges = frozenset({avoid_edges})
        assert isinstance(avoid_nodes, frozenset)
        assert isinstance(avoid_edges, frozenset)

        key = avoid_nodes, avoid_edges
        if not hasattr(self, '_avoid_reachable_cache'):
            self._avoid_reachable_cache = {}
            self._avoid_reachable_invalidated = {}
        stage_nodes = {}
        stage_edges = {}
        stage = 0
        nodes = {self.root}
        edges = set(self.root.edges)
        done_nodes = set(avoid_nodes)
        done_edges = set(avoid_edges)
        if avoid_nodes in self._avoid_reachable_cache:
            cached_nodes, cached_edges = \
                    self._avoid_reachable_cache[key]
            invalid = self._avoid_reachable_invalidated[key]
            if not invalid:
                return cached_nodes, cached_edges
        else:
            cached_nodes, cached_edges = None, None

        while True:
            if cached_nodes:
                if stage not in cached_nodes:
                    cached_nodes, cached_edges = None, None
                    continue
                invalid_nodes = cached_nodes[stage] & \
                        self._avoid_reachable_invalidated[key]
                if invalid_nodes:
                    if stage > 0:
                        done_nodes = set(cached_nodes[stage] | avoid_nodes)
                        done_edges = set(
                            cached_edges[stage-1] & self.conditionless_edges) \
                                    | avoid_edges
                        nodes = set(cached_nodes[stage])
                        edges = set(cached_edges[stage] & self.all_edges)
                        for n in invalid_nodes:
                            edges |= n.edges
                    cached_nodes, cached_edges = None, None
                    continue
                else:
                    stage_nodes[stage] = cached_nodes[stage]
                    stage_edges[stage] = cached_edges[stage]
                    if stage+1 not in cached_nodes:
                        break
                    stage += 1
                    continue

            stage_nodes[stage] = frozenset(nodes)
            stage_edges[stage] = frozenset(edges)
            for e in edges - done_edges:
                if e.is_satisfied_by(stage_nodes[stage]):
                    if e.destination not in done_nodes:
                        nodes.add(e.destination)
                    done_edges.add(e)
            for n in nodes - done_nodes:
                edges |= n.edges
                done_nodes.add(n)
            if nodes == stage_nodes[stage]:
                break
            stage += 1

        self._avoid_reachable_cache[key] = (stage_nodes, stage_edges)
        self.mark_valid_reachability_cache(key)
        assert stage_nodes is not None
        return stage_nodes, stage_edges

    def invalidate_node_reachability(self, nodes):
        if not hasattr(self, '_avoid_reachable_cache'):
            return
        for avoid_nodes in sorted(self._avoid_reachable_cache):
            self._avoid_reachable_invalidated[avoid_nodes] |= nodes

    def mark_valid_reachability_cache(self, key):
        self._avoid_reachable_invalidated[key] = set()

    def check_is_reachable_new(self, goal_node,
                               avoid_nodes=None, avoid_edges=None):
        # new method seems to be equal speed but preserves more useful info
        nodes, edges = self.get_avoid_reachable(avoid_nodes)
        if DEBUG:
            bnodes, bedges = self.get_avoid_reachable(avoid_nodes, debug=True)
            assert nodes == bnodes
            assert edges == bedges
        return goal_node in nodes[max(nodes)]

    def check_is_reachable(self, goal_node,
                           avoid_nodes=None, avoid_edges=None):
        if DEBUG and not avoid_edges:
            a = self.check_is_reachable_old(goal_node, avoid_nodes)
            b = self.check_is_reachable_new(goal_node,
                                            avoid_nodes, avoid_edges)
            assert a == b
        return self.check_is_reachable_new(goal_node, avoid_nodes, avoid_edges)

    def commit(self, version=None):
        super().commit(version)
        for n in self.nodes:
            n.commit(version)

    def rollback(self, version=None):
        super().rollback(version)
        for n in self.nodes:
            n.rollback(version)

    def verify(self):
        for n in sorted(self.nodes):
            try:
                n.verify()
            except DoorRouterException as error:
                self.problematic_nodes[n] += 1
                raise error

    def procedural_add_edge(self, strict_candidates, lenient_candidates):
        options = []
        for o in sorted(self.unconnected):
            if not o.rooted:
                continue
            require_guarantee = o.required_nodes | o.guarantee_nodes
            if require_guarantee <= self.rooted:
                options.append(o)

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

        edge_ab = a.add_edge(b, procedural=True)
        edge_ba = b.add_edge(a, procedural=True)
        self.discourage_nodes[a].add(b)
        self.discourage_nodes[b].add(a)
        self.unconnected -= {a, b}
        if DEBUG:
            print(f'ADD {a} {b}')

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
        if DEBUG:
            print(f'REMOVE {a} {b}')

    def handle_trap_doors(self):
        if self.config['trap_doors'] <= 0:
            return
        print('Adding trap doors...')
        self.verify()
        assert self.root_reachable_from == self.reachable_from_root
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
                if DEBUG:
                    print('TRAP', new_edge)
                continue
            new_destination = random.choice(candidates)
            try:
                new_edge = e.source.add_edge(new_destination,
                                             procedural=True)
                if DEBUG:
                    print('TRAP', new_edge)
                self.verify()
                if self.root_reachable_from != self.reachable_from_root:
                    raise DoorRouterException(str(new_edge))
                e.remove()
            except DoorRouterException:
                new_edge.remove()
        self.verify()
        assert self.root_reachable_from == self.reachable_from_root

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
        PROGRESS_BAR_LENGTH = 20
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

            goal_reached = self.goal_reached
            if goal_reached:
                if self.root_reachable_from >= self.reachable_from_root:
                    assert self.root_reachable_from == self.reachable_from_root
                    break

            if self.num_loops // PROGRESS_BAR_INTERVAL > previous_progress_bar:
                previous_progress_bar += 1
                if goal_reached:
                    stdout.write('+')
                else:
                    stdout.write('.')
                stdout.flush()

            if self.num_loops > self.config['retry_limit_close'] or (
                    self.num_loops > self.config['retry_limit']
                    and not goal_reached):
                t2 = time()
                raise DoorRouterException(
                    f'Failed to build maze within {self.num_loops-1} '
                    f'operations.\nTime taken: {round(t2-t1,1)} seconds.')
            backup_unconnected = set(self.unconnected)

            if DEBUG:
                self.verify()

            add_edge = False
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
                self.procedural_add_edge(strict_candidates, lenient_candidates)
            else:
                self.procedural_remove_edge()
                failures = 0

            unreachable = self.connectable - self.reachable_from_root
            unrootable = self.connectable - self.root_reachable_from
            report = f'{self.num_loops} {len(self.unconnected)}/' \
                    f'{len(unreachable)}/{len(unrootable)} {self.goal_reached}'
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
                    self.verify()
                failures += 1
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
