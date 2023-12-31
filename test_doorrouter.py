# Run this file as a module from the parent directory, i.e.:
#       python -m randomtools.test_doorrouter
from .doorrouter import Graph
from string import ascii_lowercase, ascii_uppercase
from sys import exc_info
import random
import traceback

def get_graph(labels=None):
    if labels is None:
        labels = ascii_lowercase
    g = Graph(testing=True)
    for c in labels:
        g.Node(c, g)
    root = g.Node('root', g)
    assert g.testing
    g.set_root(root)
    assert g.reduce
    return g

def load_test_data(filename):
    node_labels = set()
    edge_labels = set()
    with open(filename) as f:
        for line in f:
            line = line.strip()
            edge, condition = line.split(': ')
            condition = condition.strip('*')
            assert condition[0] == '['
            assert condition[-1] == ']'
            source, destination = edge.split('->')
            condition = condition[1:-1]
            if condition:
                labels = frozenset(condition.split(', '))
                node_labels |= set(labels)
                labels = '&'.join(labels)
            else:
                labels = None
            node_labels.add(source)
            node_labels.add(destination)
            edge_labels.add((source, destination, labels))
    node_labels = sorted(node_labels)
    edge_labels = sorted(edge_labels,
            key=lambda e: (e[0], e[1], e[2] if e[2] is not None else ''))
    random.shuffle(node_labels)
    random.shuffle(edge_labels)
    g = Graph(testing=True)
    for n in node_labels:
        n = g.Node(n, g)
    for source, destination, condition in edge_labels:
        g.add_edge(source, destination, condition=condition)
    g.set_root(g.by_label('root'))
    g.testing = False
    return g

def get_random_graph():
    g = get_graph(ascii_lowercase + ascii_uppercase)
    nodes = sorted(g.nodes)
    for n1 in nodes:
        for n2 in nodes:
            if n1 is n2:
                continue
            odds = int(round(len(nodes) ** 0.85))
            while True:
                if random.randint(0, odds) != 0:
                    break
                condition_length = random.randint(0, len(nodes))
                condition = random.sample(nodes, condition_length)
                g.add_edge(n1, n2, condition=frozenset(condition))
    g.rooted
    return g

def test_test():
    g = get_graph()
    g.add_edge('root', 'a', directed=False)
    g.add_edge('a', 'b', directed=False)
    g.add_edge('root', 'c', condition='b', directed=False)
    #assert g.reachable_from_root == g.nodes
    assert len(g.reachable_from_root) == 4
    assert g.reachable_from_root == g.root_reachable_from

def test_double_one_way1():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('root', 'b')
    g.add_edge('root', 'c', condition='a|b')
    assert g.get_by_label('c') not in g.reachable_from_root

def test_double_one_way2():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('a', 'root', condition='b')
    g.add_edge('root', 'b')
    g.add_edge('b', 'root', condition='a')
    g.add_edge('root', 'c', condition='a|b')
    assert g.get_by_label('c') not in g.reachable_from_root

def test_double_one_way3():
    g = get_graph()
    g.add_edge('root', 'a', directed=False)
    g.add_edge('root', 'b', condition='a', directed=False)
    g.add_edge('root', 'c', condition='a&b')
    assert g.get_by_label('c') in g.reachable_from_root

def test_uncertain_one_way1():
    g = get_graph()
    g.add_edge('root', 'a', directed=False)
    g.add_edge('root', 'b')
    g.add_edge('b', 'root', condition='a')
    g.add_edge('root', 'c', condition='a&b', directed=False)
    assert g.get_by_label('b') in g.reachable_from_root
    assert g.get_by_label('b') not in g.root_reachable_from
    assert g.get_by_label('c') in g.reachable_from_root
    assert g.get_by_label('c') in g.root_reachable_from

def test_uncertain_one_way2():
    g = get_graph()
    g.add_edge('root', 'a', directed=False)
    g.add_edge('root', 'b')
    g.add_edge('b', 'root', condition='a')
    g.add_edge('b', 'c', condition='a&b', directed=False)
    assert g.get_by_label('b') in g.reachable_from_root or \
            g.get_by_label('c') in g.reachable_from_root
    assert g.get_by_label('b') not in g.root_reachable_from
    assert g.get_by_label('c') not in g.root_reachable_from

def test_uncertain_one_way3():
    g = get_graph()
    g.add_edge('root', 'b')
    g.add_edge('b', 'a', directed=False)
    g.add_edge('b', 'root', condition='a')
    g.add_edge('root', 'c', condition='a&b', directed=False)
    assert g.get_by_label('b') in g.reachable_from_root
    assert g.get_by_label('c') in g.reachable_from_root
    assert g.get_by_label('b') in g.root_reachable_from
    assert g.get_by_label('c') in g.root_reachable_from

def test_uncertain_one_way4():
    g = get_graph()
    g.add_edge('root', 'a', directed=False)
    g.add_edge('root', 'b')
    g.add_edge('b', 'root', condition='c')
    g.add_edge('root', 'c', condition='a&b', directed=False)
    assert g.get_by_label('b') in g.reachable_from_root
    assert g.get_by_label('b') not in g.root_reachable_from
    assert g.get_by_label('c') not in g.root_reachable_from

def test_uncertain_condition1():
    g = get_graph()
    g.add_edge('root', 'a', directed=False)
    g.add_edge('root', 'b', directed=True)
    g.add_edge('b', 'c', condition='a', directed=False)
    g.add_edge('c', 'root', condition='a', directed=True)
    assert g.get_by_label('b') in g.reachable_from_root
    assert g.get_by_label('c') in g.reachable_from_root
    assert g.get_by_label('b') in g.get_no_return_nodes(allow_nodes=g.nodes)
    rfb, brf = g.get_by_label('b').get_reduced_guaranteed_reachable()
    assert g.get_by_label('c') in rfb
    rfc, crf = g.get_by_label('c').get_reduced_guaranteed_reachable()
    assert g.get_by_label('a') in g.get_by_label('c').guaranteed
    assert g.get_by_label('b') in rfc
    assert g.get_by_label('b') not in crf
    assert g.get_by_label('c') in g.root_reachable_from
    assert g.get_by_label('b') not in g.root_reachable_from

def test_uncertain_condition2():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('root', 'c')
    g.add_edge('a', 'c')
    g.add_edge('c', 'd', condition='a', directed=False)
    g.rooted

    rfc, crf = g.get_by_label('c').get_reduced_guaranteed_reachable()
    rfd, drf = g.get_by_label('d').get_reduced_guaranteed_reachable()
    assert g.get_by_label('d') in rfc
    assert g.get_by_label('d') in crf
    assert g.get_by_label('c') in rfd
    assert g.get_by_label('c') not in drf
    assert g.get_by_label('root') not in drf

def test_uncertain_condition3():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('root', 'c')
    g.add_edge('root', 'd')
    g.add_edge('a', 'c')
    g.add_edge('c', 'd', condition='a', directed=False)
    g.rooted

    rfc, crf = g.get_by_label('c').get_reduced_guaranteed_reachable()
    rfd, drf = g.get_by_label('d').get_reduced_guaranteed_reachable()
    assert g.get_by_label('d') in rfc
    assert g.get_by_label('d') not in crf
    assert g.get_by_label('c') in rfd
    assert g.get_by_label('c') not in drf

def test_multiple_conditions1():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('root', 'b')
    g.add_edge('a', 'c')
    g.add_edge('b', 'c')
    g.add_edge('c', 'd', condition='a', directed=False)
    g.add_edge('c', 'd', condition='b', directed=False)
    g.rooted

    assert g.by_label('d').full_guaranteed == g.by_label('c').full_guaranteed

    assert g.get_by_label('c') in g.reachable_from_root
    assert g.get_by_label('d') in g.reachable_from_root
    rfc, crf = g.get_by_label('c').get_reduced_guaranteed_reachable()
    rfd, drf = g.get_by_label('d').get_reduced_guaranteed_reachable()
    assert g.get_by_label('d') in rfc
    assert g.get_by_label('d') in crf
    assert g.get_by_label('c') in rfd
    assert g.get_by_label('c') in drf

def test_multiple_conditions2():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('root', 'b')
    g.add_edge('a', 'c')
    g.add_edge('b', 'c')
    g.add_edge('c', 'd', condition='a', directed=False)
    g.add_edge('c', 'd', condition='b', directed=False)

    g.add_edge('root', 'x')
    g.add_edge('x', 'c')
    g.add_edge('c', 'd', condition='x', directed=True)
    g.rooted

    assert g.by_label('d').full_guaranteed == g.by_label('c').full_guaranteed

    rfc, crf = g.get_by_label('c').get_reduced_guaranteed_reachable()
    rfd, drf = g.get_by_label('d').get_reduced_guaranteed_reachable()
    assert g.get_by_label('d') in rfc
    assert g.get_by_label('d') not in crf
    assert g.get_by_label('root') in crf
    assert g.get_by_label('c') in rfd
    assert g.get_by_label('c') in drf

def test_multiple_conditions3():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('root', 'b')
    g.add_edge('a', 'c')
    g.add_edge('b', 'c')
    g.add_edge('c', 'd', condition='a', directed=False)
    g.add_edge('c', 'd', condition='b', directed=False)

    g.add_edge('root', 'x')
    g.add_edge('x', 'c')
    g.add_edge('d', 'c', condition='x', directed=True)
    g.rooted

    assert g.by_label('d').full_guaranteed < g.by_label('c').full_guaranteed

    rfc, crf = g.get_by_label('c').get_reduced_guaranteed_reachable()
    rfd, drf = g.get_by_label('d').get_reduced_guaranteed_reachable()
    assert g.get_by_label('d') in rfc
    assert g.get_by_label('d') in crf
    assert g.get_by_label('c') in rfd
    assert g.get_by_label('c') not in drf
    assert g.get_by_label('root') not in drf

def test_multiple_conditions4():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('root', 'b')
    g.add_edge('a', 'c')
    g.add_edge('b', 'c')
    g.add_edge('c', 'd', condition='a', directed=False)
    g.add_edge('c', 'd', condition='b', directed=False)

    g.add_edge('c', 'd', condition='x', directed=False)
    g.rooted

    assert g.by_label('d').full_guaranteed == g.by_label('c').full_guaranteed

    rfc, crf = g.get_by_label('c').get_reduced_guaranteed_reachable()
    rfd, drf = g.get_by_label('d').get_reduced_guaranteed_reachable()
    assert g.get_by_label('d') in rfc
    assert g.get_by_label('d') in crf
    assert g.get_by_label('c') in rfd
    assert g.get_by_label('c') in drf

def test_multiple_conditions5():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('root', 'b')
    g.add_edge('a', 'c')
    g.add_edge('b', 'c')
    g.add_edge('c', 'd', condition='a', directed=False)
    g.add_edge('c', 'd', condition='b', directed=False)

    g.add_edge('c', 'd', condition='x', directed=True)
    g.rooted

    assert g.by_label('d').full_guaranteed == g.by_label('c').full_guaranteed

    rfc, crf = g.get_by_label('c').get_reduced_guaranteed_reachable()
    rfd, drf = g.get_by_label('d').get_reduced_guaranteed_reachable()
    assert g.get_by_label('d') in rfc
    assert g.get_by_label('d') in crf
    assert g.get_by_label('c') in rfd
    assert g.get_by_label('c') in drf

def test_multiple_conditions6():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('root', 'b')
    g.add_edge('a', 'c')
    g.add_edge('b', 'c')
    g.add_edge('c', 'd', condition='a', directed=False)
    g.add_edge('c', 'd', condition='b', directed=False)

    g.add_edge('d', 'c', condition='x', directed=True)
    g.rooted

    assert g.by_label('d').full_guaranteed == g.by_label('c').full_guaranteed

    rfc, crf = g.get_by_label('c').get_reduced_guaranteed_reachable()
    rfd, drf = g.get_by_label('d').get_reduced_guaranteed_reachable()
    assert g.get_by_label('d') in rfc
    assert g.get_by_label('d') in crf
    assert g.get_by_label('c') in rfd
    assert g.get_by_label('c') in drf

def test_multiple_conditions7():
    g = get_graph()
    g.add_edge('root', 'w')
    g.add_edge('root', 'x')
    g.add_edge('w', 'y')
    g.add_edge('x', 'y')
    g.add_edge('y', 'z', condition='w', directed=False)
    g.add_edge('y', 'z', condition='x', directed=False)

    g.add_edge('y', 'z', condition='i', directed=True)
    g.rooted

    assert g.by_label('z').full_guaranteed == g.by_label('y').full_guaranteed

    rfy, yrf = g.get_by_label('y').get_reduced_guaranteed_reachable()
    rfz, zrf = g.get_by_label('z').get_reduced_guaranteed_reachable()
    assert g.get_by_label('z') in rfy
    assert g.get_by_label('z') in yrf
    assert g.get_by_label('y') in rfz
    assert g.get_by_label('y') in zrf

def test_multiple_conditions_triangle01():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('a', 'b', directed=False)
    g.add_edge('b', 'c', condition='a', directed=False)
    g.add_edge('a', 'c', condition='b', directed=False)
    g.rooted
    assert g.get_by_label('c') in g.reachable_from_root
    assert g.get_by_label('c') not in g.root_reachable_from

def test_multiple_conditions_triangle02():
    g = get_graph()
    g.add_edge('root', 'b')
    g.add_edge('a', 'b', directed=False)
    g.add_edge('b', 'c', condition='a', directed=False)
    g.add_edge('a', 'c', condition='b', directed=False)
    g.rooted
    assert g.get_by_label('c') in g.reachable_from_root
    assert g.get_by_label('c') not in g.root_reachable_from

def test_multiple_conditions_triangle03():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('root', 'b')
    g.add_edge('a', 'b', directed=False)
    g.add_edge('b', 'c', condition='a', directed=False)
    g.add_edge('a', 'c', condition='b', directed=False)
    g.rooted
    assert g.get_by_label('c') in g.reachable_from_root
    assert g.get_by_label('c') not in g.root_reachable_from

def test_multiple_conditions_triangle04():
    g = get_graph()
    g.add_edge('root', 'a', directed=False)
    g.add_edge('root', 'b')
    g.add_edge('a', 'b', directed=False)
    g.add_edge('b', 'c', condition='a', directed=False)
    g.add_edge('a', 'c', condition='b', directed=False)
    g.rooted
    assert g.get_by_label('c') in g.reachable_from_root
    assert g.get_by_label('c') in g.root_reachable_from

def test_multiple_conditions_triangle05():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('a', 'c')
    g.add_edge('b', 'c')
    g.add_edge('a', 'd')
    g.add_edge('b', 'd')
    g.add_edge('c', 'e', condition='a')
    g.add_edge('d', 'e', condition='b')
    g.rooted
    assert g.get_by_label('e') in g.reachable_from_root

def test_multiple_conditions_triangle06():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('a', 'c')
    g.add_edge('b', 'c')
    g.add_edge('c', 'e', condition='a')
    g.add_edge('c', 'e', condition='b')
    g.rooted
    assert g.get_by_label('e') in g.reachable_from_root

def test_multiple_conditions_triangle07():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('a', 'b')
    g.add_edge('b', 'c')
    g.add_edge('c', 'e', condition='a&b')
    g.rooted
    assert g.get_by_label('e') in g.reachable_from_root

def test_multiple_conditions_triangle08():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('a', 'c')
    g.add_edge('a', 'b')
    g.add_edge('b', 'c')
    g.add_edge('c', 'e', condition='a&b')
    g.rooted
    assert g.get_by_label('e') in g.reachable_from_root

def test_multiple_conditions_triangle09():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('root', 'b')
    g.add_edge('root', 'c')
    g.add_edge('a', 'c', directed=False)
    g.add_edge('a', 'b', directed=False)
    g.add_edge('b', 'c', directed=False)
    g.add_edge('a', 'e', condition='b&c')
    g.add_edge('b', 'e', condition='a&c')
    g.add_edge('c', 'e', condition='a&b')
    g.rooted
    assert g.get_by_label('e') in g.reachable_from_root

def test_multiple_conditions_triangle10():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('root', 'b')
    g.add_edge('root', 'c')
    g.add_edge('a', 'c', directed=False)
    g.add_edge('a', 'b', directed=False)
    g.add_edge('b', 'c', directed=False)
    g.add_edge('a', 'e', condition='b')
    g.add_edge('a', 'e', condition='c')
    g.add_edge('b', 'e', condition='a')
    g.add_edge('b', 'e', condition='c')
    g.add_edge('c', 'e', condition='a')
    g.add_edge('c', 'e', condition='b')
    g.rooted
    assert g.get_by_label('e') in g.reachable_from_root

def test_multiple_conditions_triangle11():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('root', 'b')
    g.add_edge('a', 'b', directed=False)
    g.add_edge('b', 'c', condition='a', directed=False)
    g.add_edge('a', 'c', condition='b', directed=False)
    g.add_edge('a', 'root', condition='c')
    g.rooted
    assert g.get_by_label('c') in g.reachable_from_root
    assert g.get_by_label('c') in g.root_reachable_from

def test_multiple_conditions_triangle12():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('root', 'b')
    g.add_edge('a', 'b', directed=False)
    g.add_edge('a', 'root', condition='a&b')
    g.rooted
    assert g.get_by_label('a') in g.reachable_from_root
    assert g.get_by_label('a') in g.root_reachable_from
    assert g.get_by_label('b') in g.reachable_from_root
    assert g.get_by_label('b') in g.root_reachable_from

def test_multiple_conditions_triangle13():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('root', 'b')
    g.add_edge('root', 'x', condition='c')
    g.add_edge('a', 'b', directed=False)
    g.add_edge('b', 'c', condition='a', directed=False)
    g.add_edge('a', 'c', condition='b', directed=False)
    g.add_edge('a', 'x', condition='c')
    g.rooted
    assert g.get_by_label('c') in g.reachable_from_root

def test_multiple_conditions_triangle14():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('root', 'b')
    g.add_edge('a', 'b', directed=False)
    g.add_edge('b', 'c', condition='a', directed=False)
    g.add_edge('a', 'c', condition='b', directed=False)
    g.add_edge('a', 'x', condition='c')
    g.add_edge('x', 'root', condition='c')
    g.rooted
    assert g.get_by_label('c') in g.reachable_from_root
    assert g.get_by_label('c') in g.root_reachable_from

def test_multiple_uncertain_conditions1():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('root', 'b')
    g.add_edge('root', 'x', directed=False)
    g.add_edge('a', 'c')
    g.add_edge('b', 'c')
    g.add_edge('c', 'd', condition='a', directed=False)
    g.add_edge('c', 'd', condition='b', directed=False)

    g.add_edge('c', 'd', condition='x', directed=True)
    g.rooted

    rfc, crf = g.get_by_label('c').get_reduced_guaranteed_reachable()
    rfd, drf = g.get_by_label('d').get_reduced_guaranteed_reachable()
    assert g.get_by_label('d') in rfc
    assert g.get_by_label('d') in crf
    assert g.get_by_label('c') in rfd
    assert g.get_by_label('c') in drf

def test_multiple_uncertain_conditions2():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('root', 'b')
    g.add_edge('root', 'x', directed=False)
    g.add_edge('a', 'c')
    g.add_edge('b', 'c')
    g.add_edge('c', 'd', condition='a', directed=False)
    g.add_edge('c', 'd', condition='b', directed=False)

    g.add_edge('d', 'c', condition='x', directed=True)
    g.rooted

    rfc, crf = g.get_by_label('c').get_reduced_guaranteed_reachable()
    rfd, drf = g.get_by_label('d').get_reduced_guaranteed_reachable()
    assert g.get_by_label('d') in rfc
    assert g.get_by_label('d') in crf
    assert g.get_by_label('c') in rfd
    assert g.get_by_label('c') in drf

def test_multiple_uncertain_conditions3():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('root', 'b')
    g.add_edge('root', 'x', directed=False)
    g.add_edge('a', 'c')
    g.add_edge('b', 'c')
    g.add_edge('c', 'd', condition='a', directed=False)
    g.add_edge('c', 'd', condition='b', directed=False)

    g.add_edge('c', 'd', condition='x', directed=False)
    g.rooted

    rfc, crf = g.get_by_label('c').get_reduced_guaranteed_reachable()
    rfd, drf = g.get_by_label('d').get_reduced_guaranteed_reachable()
    assert g.get_by_label('d') in rfc
    assert g.get_by_label('d') in crf
    assert g.get_by_label('c') in rfd
    assert g.get_by_label('c') in drf

def test_multiple_uncertain_conditions4():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('root', 'c')
    g.add_edge('root', 'x', directed=False)
    g.add_edge('a', 'c')
    g.add_edge('c', 'd', condition='a', directed=False)
    g.add_edge('c', 'd', condition='b', directed=False)

    g.add_edge('c', 'd', condition='x', directed=False)
    g.rooted

    rfc, crf = g.get_by_label('c').get_reduced_guaranteed_reachable()
    rfd, drf = g.get_by_label('d').get_reduced_guaranteed_reachable()
    assert g.get_by_label('d') in rfc
    assert g.get_by_label('d') in crf
    assert g.get_by_label('c') in rfd
    assert g.get_by_label('c') not in drf
    assert g.get_by_label('root') not in drf

def test_multiple_uncertain_conditions5():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('root', 'c')
    g.add_edge('root', 'x', directed=False)
    g.add_edge('a', 'c')
    g.add_edge('c', 'd', condition='a', directed=False)
    g.add_edge('c', 'd', condition='b', directed=False)

    g.add_edge('c', 'd', condition='x', directed=True)
    g.rooted

    rfc, crf = g.get_by_label('c').get_reduced_guaranteed_reachable()
    rfd, drf = g.get_by_label('d').get_reduced_guaranteed_reachable()
    assert g.get_by_label('d') in rfc
    assert g.get_by_label('d') not in crf
    assert g.get_by_label('c') in rfd
    assert g.get_by_label('c') not in drf

def test_multiple_uncertain_conditions6():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('root', 'b')
    g.add_edge('root', 'x', directed=False)
    g.add_edge('a', 'c')
    g.add_edge('b', 'c')
    g.add_edge('c', 'd', condition='a', directed=True)
    g.add_edge('c', 'd', condition='b', directed=True)

    g.add_edge('c', 'd', condition='x', directed=False)
    g.rooted

    rfc, crf = g.get_by_label('c').get_reduced_guaranteed_reachable()
    rfd, drf = g.get_by_label('d').get_reduced_guaranteed_reachable()
    assert g.get_by_label('d') in rfc
    assert g.get_by_label('d') not in crf
    assert g.get_by_label('c') in rfd
    assert g.get_by_label('c') in drf

def test_distant_condition():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('a', 'b')
    g.add_edge('b', 'c')
    g.add_edge('c', 'x', directed=False)
    g.add_edge('c', 'b', condition='x')
    g.add_edge('b', 'a', condition='x')
    g.add_edge('a', 'root', condition='x')
    g.rooted

    rfr, rrf = g.root.get_reduced_guaranteed_reachable()
    assert g.get_by_label('x') in rfr
    assert g.get_by_label('x') in rrf

def test_distant_uncertain_condition1():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('a', 'b')
    g.add_edge('b', 'y', directed=False)
    g.add_edge('b', 'c')
    g.add_edge('c', 'x', condition='y', directed=False)
    g.add_edge('c', 'b', condition='x')
    g.add_edge('b', 'a', condition='x')
    g.add_edge('a', 'root', condition='x')
    g.rooted

    rfr, rrf = g.root.get_reduced_guaranteed_reachable()
    assert g.get_by_label('x') in rfr
    assert g.get_by_label('x') in rrf

def test_distant_uncertain_condition2():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('a', 'b')
    g.add_edge('b', 'y', directed=False)
    g.add_edge('b', 'c')
    g.add_edge('c', 'x', directed=False)
    g.add_edge('c', 'b', condition='x')
    g.add_edge('b', 'a', condition='x')
    g.add_edge('a', 'root', condition='x&y')
    g.rooted

    rfr, rrf = g.root.get_reduced_guaranteed_reachable()
    assert g.get_by_label('x') in rfr
    assert g.get_by_label('x') in rrf

def test_distant_uncertain_condition3():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('a', 'b')
    g.add_edge('b', 'y', directed=False)
    g.add_edge('b', 'c')
    g.add_edge('c', 'x', condition='y', directed=False)
    g.add_edge('c', 'b', condition='x&y')
    g.add_edge('b', 'a', condition='x')
    g.add_edge('a', 'root', condition='x')
    g.rooted

    rfr, rrf = g.root.get_reduced_guaranteed_reachable()
    assert g.get_by_label('x') in rfr
    assert g.get_by_label('x') in rrf
    assert g.get_by_label('c') in rfr
    assert g.get_by_label('c') not in rrf

def test_distant_uncertain_condition4():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('a', 'b')
    g.add_edge('b', 'y', directed=False)
    g.add_edge('b', 'c')
    g.add_edge('c', 'x', condition='y', directed=False)
    g.add_edge('c', 'b', condition='x')
    g.add_edge('b', 'a', condition='x')
    g.add_edge('a', 'root', condition='x&y')
    g.rooted

    rfr, rrf = g.root.get_reduced_guaranteed_reachable()
    assert g.get_by_label('x') in rfr
    assert g.get_by_label('x') in rrf
    assert g.get_by_label('c') in rfr
    assert g.get_by_label('c') not in rrf

def test_distant_uncertain_condition5():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('a', 'b')
    g.add_edge('b', 'y', directed=False)
    g.add_edge('b', 'c')
    g.add_edge('c', 'x', directed=False)
    g.add_edge('c', 'b', condition='y')
    g.add_edge('b', 'a', condition='x')
    g.add_edge('a', 'root')
    g.rooted

    rfr, rrf = g.root.get_reduced_guaranteed_reachable()
    assert g.get_by_label('x') in rfr
    assert g.get_by_label('x') not in rrf
    assert g.get_by_label('c') in rfr
    assert g.get_by_label('c') not in rrf

def test_distant_uncertain_condition6():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('a', 'b')
    g.add_edge('b', 'y', directed=False)
    g.add_edge('b', 'c', condition='y')
    g.add_edge('c', 'x', directed=False)
    g.add_edge('c', 'b', condition='y')
    g.add_edge('b', 'a', condition='x')
    g.add_edge('a', 'root')
    g.rooted

    rfr, rrf = g.root.get_reduced_guaranteed_reachable()
    assert g.get_by_label('x') in rfr
    assert g.get_by_label('x') in rrf
    assert g.get_by_label('c') in rfr
    assert g.get_by_label('c') in rrf

def test_distant_uncertain_condition7():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('a', 'b')
    g.add_edge('b', 'y', directed=False)
    g.add_edge('b', 'z', condition='y', directed=False)
    g.add_edge('b', 'c', condition='y')
    g.add_edge('c', 'x', condition='z', directed=False)
    g.add_edge('c', 'b', condition='x')
    g.add_edge('b', 'a', condition='x')
    g.add_edge('a', 'root', condition='x&y&z')
    g.rooted

    rfr, rrf = g.root.get_reduced_guaranteed_reachable()
    assert g.get_by_label('x') in rfr
    assert g.get_by_label('x') in rrf
    assert g.get_by_label('c') in rfr
    assert g.get_by_label('c') not in rrf

def test_backtracking():
    g = get_graph()
    g.add_edge('root', 'a', directed=False)
    g.add_edge('root', 'b', directed=False)
    g.add_edge('a', 'c', directed=False)
    g.add_edge('b', 'd', condition='c', directed=False)
    g.add_edge('c', 'e', condition='d', directed=False)
    g.add_edge('d', 'f', condition='e', directed=False)
    g.rooted
    rfr, rrf = g.root.get_reduced_guaranteed_reachable()
    assert g.get_by_label('f') in rfr
    assert g.get_by_label('f') in rrf
    assert len(rfr) == len({'root', 'a', 'b', 'c', 'd', 'e', 'f'})
    assert rrf == rfr

def test_random_equivalent_nodes():
    g = get_random_graph()
    g.rooted
    rfr, rrf = g.root.get_reduced_guaranteed_reachable()
    nodes = sorted(rfr)
    set_lengths = set()
    for n1 in nodes:
        assert n1.free_travel_nodes == n1.get_free_travel_nodes()
        assert n1.equivalent_nodes == n1.get_equivalent_nodes()
        set_lengths.add(len(n1.free_travel_nodes))
        for n2 in nodes:
            if n2 not in n1.free_travel_nodes:
                assert not n1.free_travel_nodes & n2.free_travel_nodes
                if n2 not in n1.equivalent_nodes:
                    assert not n1.equivalent_nodes & n2.equivalent_nodes
                    assert n1.equivalent_nodes != n2.equivalent_nodes
                else:
                    assert n1.equivalent_nodes == n2.equivalent_nodes
            else:
                assert n2 in n1.equivalent_nodes
                assert n1.equivalent_nodes == n2.equivalent_nodes

def test_circular_dependency():
    g = get_graph()
    g.add_edge('root', 'a')
    g.add_edge('root', 'b')
    g.add_edge('root', 'c')
    g.add_edge('root', 'x')
    g.add_edge('root', 'y')
    g.add_edge('root', 'z')
    g.add_edge('a', 'b', condition='y&z', directed=False)
    g.add_edge('b', 'c', condition='x&z', directed=False)
    g.add_edge('c', 'a', condition='x&y', directed=False)
    g.add_edge('a', 'x', condition='b', directed=False)
    g.add_edge('b', 'y', condition='c', directed=False)
    g.add_edge('c', 'z', condition='a', directed=False)
    g.rooted
    rfr, rrf = g.root.get_reduced_guaranteed_reachable()
    assert len(rfr) == 7
    assert len(rrf) == 1

def test_no_add_root1():
    g = Graph(testing=True)
    root = g.Node('1d1-001', g)
    g.set_root(root)
    try:
        a = g.Node('049-001', g)
        b = g.Node('0b5-00c', g)
    except NotImplementedError:
        return
    g.add_edge(a, b)
    g.add_edge(a, b)
    assert False

def test_no_add_root2():
    g = Graph(testing=True)
    root = g.Node('1d1-001', g)
    a = g.Node('049-001', g)
    b = g.Node('0b5-00c', g)
    g.set_root(root)
    g.add_edge(a, b)
    g.add_edge(a, b)

def test_loop1():
    g = get_graph()
    g.add_edge('root', 'a', directed=False)
    g.add_edge('a', 'b', directed=True)
    g.add_edge('b', 'c', directed=True)
    g.add_edge('c', 'a', directed=True)
    g.add_edge('b', 'x', directed=False)
    g.add_edge('c', 'y', condition='x', directed=True)
    g.reduce = False
    g.clear_rooted_cache()
    g.rooted
    rfn, nrf = g.root.get_guaranteed_reachable()
    assert not hasattr(g, 'reduced_graph')
    assert g.by_label('y') in rfn

def test_graph_reduction01():
    g = get_graph()
    g.add_edge('root', 'b', directed=False)
    g.add_edge('root', 'c', directed=True)
    g.add_edge('c', 'root', condition='b', directed=True)
    g.rooted
    rfr, rrf = g.root.get_guaranteed_reachable()
    rfc, crf = g.get_by_label('c').get_reduced_guaranteed_reachable()
    assert g.root in rfc
    assert g.root in crf
    assert g.get_by_label('c') in rfr
    assert g.get_by_label('c') not in rrf

def test_graph_reduction02():
    g = get_graph()
    g.add_edge('root', 'a', directed=False)
    g.add_edge('root', 'b', directed=False)
    g.add_edge('a', 'b', directed=False)
    g.add_edge('a', 'c', directed=True)
    g.add_edge('c', 'root', condition='b', directed=True)
    g.clear_rooted_cache()
    g.reduced_graph = g.get_reduced_graph()
    g.rooted
    rfr, rrf = g.root.get_reduced_guaranteed_reachable()
    rfc, crf = g.get_by_label('c').get_reduced_guaranteed_reachable()
    assert g.root in rfc
    assert g.root in crf
    assert g.get_by_label('c') in rfr
    assert g.get_by_label('c') not in rrf

def test_graph_reduction03():
    g = get_graph()
    g.add_edge('root', 'a', directed=False)
    g.add_edge('a', 'b', directed=False)
    g.add_edge('b', 'c', directed=False)
    g.add_edge('c', 'd', directed=True)
    g.add_edge('d', 'e', condition='b', directed=False)
    g.clear_rooted_cache()
    g.reduced_graph = g.get_reduced_graph()
    g.rooted
    assert g.reduced_graph.get_by_label('b') in \
            g.reduced_graph.conditional_nodes
    assert g.get_by_label('b') in g.get_by_label('d').guaranteed
    assert g.reduced_graph.get_by_label('b') in \
            g.reduced_graph.get_by_label('d').guaranteed

def test_graph_reduction04():
    g = get_graph()
    g.add_edge('root', 'a', directed=False)
    g.add_edge('a', 'b', directed=False)
    g.add_edge('b', 'c', directed=False)
    g.add_edge('a', 'c', directed=False)
    g.add_edge('c', 'd', directed=True)
    g.add_edge('d', 'e', condition='b', directed=False)
    g.clear_rooted_cache()
    g.reduced_graph = g.get_reduced_graph()
    g.rooted
    assert g.reduced_graph.get_by_label('b') in \
            g.reduced_graph.conditional_nodes
    assert g.get_by_label('b') not in g.get_by_label('d').guaranteed
    assert g.reduced_graph.get_by_label('b') not in \
            g.reduced_graph.get_by_label('d').guaranteed

def test_graph_reduction05():
    g = get_graph()
    g.add_edge('root', 'a', directed=True)
    g.add_edge('root', 'z', directed=True)
    g.add_edge('a', 'b', directed=False)
    g.add_edge('z', 'y', directed=False)
    g.add_edge('y', 'b', directed=True)
    g.add_edge('b', 'y', condition='q', directed=False)

    g.clear_rooted_cache()
    g.reduced_graph = g.get_reduced_graph()
    g.rooted
    rfn, nrf = g.root.get_guaranteed_reachable()
    rfx, xrf = g.root.get_reduced_guaranteed_reachable()
    rfn2, n2rf = g.get_by_label('a').get_guaranteed_reachable()
    rfx2, x2rf = g.get_by_label('a').get_reduced_guaranteed_reachable()
    assert rfn == rfx
    assert nrf == xrf
    assert rfn2 == rfx2
    assert n2rf == x2rf

def test_graph_reduction06():
    g = get_graph()
    g.add_edge('root', 'h', directed=False)
    g.add_edge('h', 'g', directed=False)
    g.add_edge('g', 'i', directed=False)
    g.add_edge('i', 'j', directed=False)
    g.add_edge('j', 'f', directed=False)
    g.add_edge('f', 'e', directed=False)
    g.add_edge('e', 'd', directed=False)
    g.add_edge('d', 'b', directed=True)
    g.add_edge('d', 'c', directed=True)
    g.add_edge('b', 'c', directed=True)
    g.add_edge('c', 'd', condition='z', directed=True)
    g.add_edge('b', 'a', directed=False)
    g.add_edge('c', 's', directed=False)
    g.add_edge('s', 't', condition='k&m&q&s&v&x', directed=False)
    g.add_edge('t', 'u', condition='k&m&q&s&v&x', directed=False)
    g.add_edge('t', 'w', directed=False)
    g.add_edge('w', 'v', directed=False)
    g.add_edge('s', 'u', directed=False)
    g.add_edge('m', 'u', directed=False)
    g.add_edge('m', 'n', directed=False)
    g.add_edge('n', 'q', directed=False)
    g.add_edge('q', 'r', directed=True)
    g.add_edge('r', 'q', condition='z', directed=True)
    g.add_edge('r', 'x', directed=False)
    g.add_edge('x', 'y', directed=False)
    g.add_edge('y', 'k', directed=False)
    g.add_edge('k', 'l', directed=False)
    g.add_edge('l', 'o', directed=False)
    g.add_edge('o', 'p', directed=False)
    g.add_edge('p', 'v', directed=False)

    g.clear_rooted_cache()
    g.reduced_graph = g.get_reduced_graph()
    g.rooted
    rfn, nrf = g.root.get_guaranteed_reachable()
    rfx, xrf = g.root.get_reduced_guaranteed_reachable()
    rfn2, n2rf = g.get_by_label('b').get_guaranteed_reachable()
    rfx2, x2rf = g.get_by_label('b').get_reduced_guaranteed_reachable()
    assert rfn == rfx
    assert nrf == xrf
    assert rfn2 == rfx2
    assert n2rf == x2rf

def test_graph_reduction07():
    g = get_graph()
    g.add_edge('root', 'a', directed=False)
    g.add_edge('a', 'b', directed=False)
    g.add_edge('b', 'c', directed=True)
    g.add_edge('c', 'b', condition='a', directed=True)

    g.clear_rooted_cache()
    g.rooted
    rfn, nrf = g.root.get_guaranteed_reachable()
    rfx, xrf = g.root.get_reduced_guaranteed_reachable()
    assert rfn == rfx
    assert nrf == xrf

def test_graph_reduction08():
    g = get_graph()
    assert not hasattr(g, 'reduced_graph')
    g.reduce = False
    g.by_label('c').add_guarantee(g.by_label('b'))
    g.add_edge('root', 'a', directed=False)
    g.add_edge('a', 'b', directed=False)
    g.add_edge('a', 'c', directed=False)
    g.clear_rooted_cache()
    g.rooted
    assert not hasattr(g, 'reduced_graph')
    assert g.by_label('b') not in g.by_label('c').guaranteed

def test_graph_reduction09():
    g = get_graph()
    assert not hasattr(g, 'reduced_graph')
    g.reduce = True
    g.by_label('c').add_guarantee(g.by_label('b'))
    g.add_edge('root', 'a', directed=False)
    g.add_edge('a', 'b', directed=False)
    g.add_edge('a', 'c', directed=False)
    g.clear_rooted_cache()
    g.rooted
    assert hasattr(g, 'reduced_graph')
    assert g.by_label('b') not in g.by_label('c').guaranteed

def test_graph_reduction10():
    g = get_graph()
    g.reduce = True
    g.add_edge('root', 'a', directed=False)
    g.add_edge('a', 'b', directed=False)
    g.add_edge('a', 'c', directed=False)
    g.add_edge('b', 'c', directed=False)
    g.add_edge('b', 'd', directed=False)
    g.rooted
    assert hasattr(g, 'reduced_graph')
    assert g.by_label('a') in g.by_label('d').guaranteed
    assert g.by_label('b') in g.by_label('d').guaranteed
    assert g.by_label('c') not in g.by_label('d').guaranteed

def test_graph_reduction11():
    g = get_graph()
    g.add_edge('root', 'a', directed=False)
    g.add_edge('a', 'b', directed=True)
    g.add_edge('b', 'c', directed=True)
    g.add_edge('c', 'a', directed=True)
    g.add_edge('b', 'x', directed=False)
    g.add_edge('c', 'y', condition='x', directed=True)
    g.reduce = False
    g.clear_rooted_cache()
    g.rooted
    rfn, nrf = g.root.get_guaranteed_reachable()
    assert not hasattr(g, 'reduced_graph')
    g.reduce = True
    g.clear_rooted_cache()
    g.rooted
    assert hasattr(g, 'reduced_graph')
    rfx, xrf = g.root.get_reduced_guaranteed_reachable()
    assert g.by_label('y') in rfn
    assert g.by_label('y') in rfx
    assert rfn == rfx
    assert nrf == xrf

def test_graph_reduction12():
    g = get_graph()
    g.add_edge('root', 'b', directed=False)
    g.add_edge('c', 'root', condition='b', directed=False)
    g.rooted
    rfr, rrf = g.root.get_guaranteed_reachable()
    rfc, crf = g.get_by_label('c').get_reduced_guaranteed_reachable()
    assert g.root in rfc
    assert g.root in crf
    assert g.get_by_label('c') in rfr
    assert g.get_by_label('c') in rrf

def test_graph_reduction13():
    g = get_graph()
    g.add_edge('root', 'a', directed=True)
    g.add_edge('a', 'b', directed=False)
    g.add_edge('b', 'c', directed=False)
    g.add_edge('d', 'e', directed=False)
    g.add_edge('e', 'f', directed=False)
    g.add_edge('b', 'd', directed=True)
    g.add_edge('e', 'h', directed=True)
    g.add_edge('g', 'b', directed=True)
    g.add_edge('h', 'i', directed=True)
    g.add_edge('a', 'z', condition='f', directed=True)
    g.add_edge('d', 'g', condition='root&c', directed=True)
    g.add_edge('x', 'y', condition='z', directed=True)
    g.reduce = False
    g.clear_rooted_cache()
    g.rooted
    rfn, nrf = g.root.get_guaranteed_reachable()
    assert not hasattr(g, 'reduced_graph')
    assert g.by_label('z') in rfn
    g.reduce = True
    g.clear_rooted_cache()
    g.rooted
    assert hasattr(g, 'reduced_graph')
    rfx, xrf = g.root.get_reduced_guaranteed_reachable()
    assert g.by_label('z') in rfx
    assert rfn == rfx
    assert nrf == xrf

def test_guarantees1():
    g = get_graph()
    g.add_edge('root', 'a', directed=True)
    g.add_edge('a', 'b', directed=True)
    g.add_edge('a', 'c', directed=True)
    g.add_edge('b', 'd', directed=True)
    g.add_edge('c', 'e', directed=True)
    g.add_edge('d', 'f', directed=True)
    g.add_edge('e', 'g', directed=True)
    g.add_edge('f', 'h', directed=True)
    g.add_edge('h', 'i', directed=True)
    g.add_edge('g', 'j', directed=True)
    g.add_edge('g', 'k', condition='x', directed=True)
    g.add_edge('i', 'l', directed=True)
    g.add_edge('j', 'k', directed=True)
    g.add_edge('l', 'm', directed=True)
    g.add_edge('m', 'x', directed=True)
    g.reduce = False
    g.clear_rooted_cache()
    g.rooted
    assert g.by_label('j') in g.by_label('k').guaranteed

def test_guarantees2():
    g = get_graph()
    g.add_edge('root', 'a', directed=True)
    g.add_edge('a', 'b', directed=True)
    g.add_edge('a', 'c', directed=True)
    g.add_edge('b', 'd', directed=True)
    g.add_edge('c', 'e', directed=True)
    g.add_edge('d', 'f', directed=True)
    g.add_edge('e', 'g', directed=True)
    g.add_edge('f', 'h', directed=True)
    g.add_edge('h', 'i', directed=True)
    g.add_edge('g', 'j', directed=True)
    g.add_edge('g', 'k', condition='x', directed=True)
    g.add_edge('i', 'l', directed=True)
    g.add_edge('j', 'k', directed=True)
    g.add_edge('l', 'm', directed=True)
    g.add_edge('m', 'x', directed=True)
    g.add_edge('x', 'g', condition='y', directed=True)
    g.add_edge('root', 'y', directed=False)
    g.reduce = False
    g.clear_rooted_cache()
    g.rooted
    assert g.by_label('x') in g.rooted
    assert g.by_label('g') in g.rooted
    assert g.by_label('k') in g.rooted
    assert g.by_label('j') not in g.by_label('k').guaranteed

def test_guarantees3():
    g = get_graph()
    g.add_edge('root', 'a', directed=True)
    g.add_edge('a', 'b', directed=True)
    g.add_edge('a', 'c', directed=True)
    g.add_edge('b', 'd', directed=True)
    g.add_edge('c', 'e', directed=True)
    g.add_edge('d', 'f', directed=True)
    g.add_edge('e', 'g', directed=True)
    g.add_edge('f', 'h', directed=True)
    g.add_edge('h', 'i', directed=True)
    g.add_edge('g', 'j', directed=True)
    g.add_edge('g', 'k', condition='x', directed=True)
    g.add_edge('i', 'l', directed=True)
    #g.add_edge('j', 'k', directed=True)
    g.add_edge('l', 'm', directed=True)
    g.add_edge('m', 'x', directed=True)
    g.add_edge('x', 'g', condition='y', directed=True)
    g.add_edge('root', 'y', directed=False)
    g.reduce = False
    g.clear_rooted_cache()
    g.rooted
    assert g.by_label('x') in g.rooted
    assert g.by_label('g') in g.rooted
    assert g.by_label('k') in g.rooted
    assert g.by_label('j') not in g.by_label('k').guaranteed

def test_graph_reduction_guarantees1():
    g = get_graph()
    g.add_edge('root', 'a', directed=True)
    g.add_edge('a', 'b', directed=False)
    g.add_edge('b', 'c', directed=False)
    g.add_edge('b', 'd', directed=True)
    g.add_edge('c', 'e', directed=True)
    g.add_edge('d', 'f', directed=False)
    g.add_edge('e', 'g', directed=False)
    g.add_edge('f', 'h', directed=False)
    g.add_edge('f', 'i', directed=True)
    g.add_edge('g', 'j', directed=True)
    g.add_edge('i', 'k', directed=True)
    g.add_edge('j', 'l', directed=False)
    g.add_edge('k', 'm', directed=True)
    g.add_edge('l', 'n', directed=True)
    g.add_edge('m', 'o', directed=True)
    g.add_edge('n', 'p', directed=True)
    g.add_edge('n', 'q', condition='x', directed=True)
    g.add_edge('o', 'r', directed=True)
    g.add_edge('p', 's', directed=True)
    g.add_edge('q', 's', directed=False)
    g.add_edge('r', 't', directed=True)
    g.add_edge('t', 'x', directed=True)
    g.reduce = False
    g.clear_rooted_cache()
    g.rooted
    rfn, nrf = g.root.get_guaranteed_reachable()
    assert g.by_label('p') in g.by_label('s').guaranteed
    guarantees = {n: n.guaranteed for n in rfn}
    assert not hasattr(g, 'reduced_graph')
    g.reduce = True
    g.clear_rooted_cache()
    g.clear_node_guarantees()
    g.rooted
    assert hasattr(g, 'reduced_graph')
    rfx, xrf = g.root.get_reduced_guaranteed_reachable()
    assert g.reduced_graph.node_mapping[g.by_label('p')] in \
            g.reduced_graph.node_mapping[g.by_label('s')].guaranteed
    assert g.by_label('p') in g.by_label('s').guaranteed
    for n in sorted(rfx):
        assert n.guaranteed >= guarantees[n]
    assert rfn == rfx
    assert nrf == xrf

def test_graph_reductionx():
    return
    g = get_graph()
    g.add_edge('root', 'a', directed=True)
    g.add_edge('a', 'b', directed=False)
    g.add_edge('a', 'z', condition='h', directed=True)
    g.add_edge('b', 'c', directed=True)
    g.add_edge('b', 'd', directed=False)
    g.add_edge('c', 'e', directed=False)
    g.add_edge('c', 'f', condition='root&j', directed=True)
    g.add_edge('d', 'g', directed=False)
    g.add_edge('e', 'h', directed=False)
    g.add_edge('e', 'i', directed=True)
    g.add_edge('f', 'd', directed=True)
    g.add_edge('g', 'b', directed=False)
    g.add_edge('g', 'j', directed=False)
    g.add_edge('i', 'k', directed=True)
    g.add_edge('x', 'y', condition='z', directed=True)
    g.reduce = True
    g.clear_rooted_cache()
    g.rooted

def test_custom():
    g = load_test_data('test_edge_data.txt')
    g.reduce = True
    g.clear_rooted_cache()
    g.rooted
    return


if __name__ == '__main__':
    #test_custom()
    #test_uncertain_one_way1()
    #test_multiple_uncertain_conditions1()
    #test_multiple_uncertain_conditions2()
    #test_graph_reduction13()
    #test_custom()
    #exit(0)
    total = 0
    failed_tests = []
    for fname, f in sorted(globals().items()):
        if not isinstance(f, type(get_graph)):
            continue
        if not fname.startswith('test_'):
            continue
        if fname.startswith('test_random_'):
            num_trials = 10
        else:
            num_trials = 1
        for _ in range(num_trials):
            try:
                f()
                msg = f'. {fname}'
            except AssertionError:
                _, _, tb = exc_info()
                tb_info = traceback.extract_tb(tb)
                filename, line, func, text = tb_info[-1]
                error = f'{line}: {text}'[:40]
                msg = f'x {fname} - {error}'
                failed_tests.append((fname, error))
            except Exception:
                _, _, tb = exc_info()
                tb_info = traceback.extract_tb(tb)
                filename, line, func, text = tb_info[-1]
                error = f'{line}: {text}'[:40]
                msg = f'E {fname} - {error}'
                failed_tests.append((fname, error))
            total += 1
            print(msg)
    print(f'Failed {len(failed_tests)}/{total} tests:')
    for fname, error in failed_tests:
        print(' ', fname, error)
