from randomtools.utils import utilrandom as random
from collections import defaultdict
from itertools import product

class ItemRouterException(Exception): pass

class ItemRouter:
    def __init__(self, requirefile):
        self.definitions = set([])
        self.assign_conditions = {}
        self.assignments = {}

        created_lambdas = []
        f = open(requirefile)
        for line in f.readlines():
            line = line.strip()
            if not line or line[0] == '#':
                continue
            while '  ' in line:
                line = line.replace('  ', ' ')

            if line.startswith(".def "):
                line = line[5:]
                definition = True
            else:
                definition = False

            try:
                label, reqs = line.split(' ', 1)
            except ValueError:
                continue

            if definition:
                self.definitions.add(label)
            self.assign_conditions[label] = reqs

        f.close()
        self.requirements = set([r for label in self.assign_conditions
                                 for r in self.get_requirements(label)])

    def get_simplified_requirements(self, label):
        if not hasattr(self, "_previous_simplified"):
            self._previous_simplified = {}
        if label in self._previous_simplified:
            return self._previous_simplified[label]
        conditions = self.assign_conditions[label]
        if conditions == '*':
            return set([])
        requirements = set([])
        for or_cond in conditions.split('|'):
            subreqs = []
            for and_cond in or_cond.split('&'):
                if and_cond in self.definitions:
                    subreqs.append(
                        self.get_simplified_requirements(and_cond))
                else:
                    subreqs.append(set([frozenset([and_cond])]))

            subreqs = [s for s in subreqs if s]
            for permutation in sorted(product(*subreqs)):
                newsubreqs = set([])
                for p in permutation:
                    newsubreqs |= p
                assert all([isinstance(n, basestring) for n in newsubreqs])
                requirements.add(frozenset(newsubreqs))

        requirements = set([r for r in requirements if r])
        for r1 in sorted(requirements):
            for r2 in sorted(requirements):
                if r1 < r2 and r2 in requirements:
                    requirements.remove(r2)

        assert isinstance(requirements, set)
        assert all([isinstance(r, frozenset) for r in requirements])
        self._previous_simplified[label] = requirements
        return self.get_simplified_requirements(label)


    def check_assignable(self, label):
        requirements = self.get_simplified_requirements(label)
        if not requirements:
            return True
        for and_reqs in requirements:
            for r in and_reqs:
                if r not in self.assigned_items:
                    break
            else:
                return True
        return False

    def get_total_requirements(self, label, cached=True):
        total = set([])
        for r in self.get_simplified_requirements(label):
            total |= r
        return total

    def get_requirements(self, label):
        if not hasattr(self, '_req_cache'):
            self._req_cache = {}
        if label in self._req_cache:
            return self._req_cache[label]

        requirements = self.get_total_requirements(label)

        self._req_cache[label] = requirements - self.assigned_items
        return self.get_requirements(label)

    @property
    def ranked_requirements(self):
        unreachables = self.unreachable_locations
        counts = {}
        counts = [(len([u for u in unreachables
                        if req in self.get_requirements(u)]),
                   random.random(), req)
                  for req in self.requirements]
        return [req for (count, _, req) in sorted(counts)
                if count > 0 and req not in self.assigned_items]

    @property
    def assigned_items(self):
        return set(self.assignments.values())

    @property
    def assigned_locations(self):
        return set(self.assignments.keys())

    @property
    def assignable_locations(self):
        assignable = set([k for k in self.assign_conditions if
                          k not in self.definitions and
                          self.check_assignable(k)])
        assignable -= self.assigned_locations
        return assignable

    def get_assigned_location(self, item):
        for key, value in self.assignments.items():
            if value == item:
                return key
        return None

    def get_item_unlocked_locations(self, items):
        if isinstance(items, basestring):
            items = [items]
        baseline_locations = self.assignable_locations
        for item in items:
            key = "_temp_%s" % item
            self.assignments[key] = item
        unlocked_locations = self.assignable_locations - baseline_locations
        for item in items:
            key = "_temp_%s" % item
            del(self.assignments[key])
        return unlocked_locations

    @property
    def unreachable_locations(self):
        return set([
            k for k in self.assign_conditions if
            k not in self.assignable_locations and
            k not in self.assigned_locations and
            k not in self.definitions])

    def sort_by_item_usage(self, locations):
        fail_counter = defaultdict(int)
        for item in self.assigned_items:
            remember_location = self.get_assigned_location(item)
            del(self.assignments[remember_location])
            assignable_locations = self.assignable_locations
            for l in locations:
                if l not in assignable_locations:
                    fail_counter[l] += 1
            self.assignments[remember_location] = item
        locations = sorted(sorted(locations),
                           key=lambda l: (fail_counter[l],
                                          self.get_location_rank(l),
                                          random.random()))
        return locations

    def assign_item(self, item, aggression=3):
        assignable_locations = self.assignable_locations
        if not assignable_locations:
            self.force_custom()
            raise ItemRouterException("No assignable locations: %s." % item)

        new_locations = self.get_item_unlocked_locations(item)
        if not new_locations:
            aggression = max(aggression-1, 1)

        max_rank = max(self.location_ranks)
        candidates = []
        for i in xrange(max_rank-1):
            temp = self.location_ranks[i] & assignable_locations
            candidates += temp
        candidates = (self.sort_by_item_usage(candidates) +
                      self.sort_by_item_usage(
                          (self.location_ranks[max_rank-1] |
                           self.location_ranks[max_rank]) &
                          assignable_locations))

        max_index = len(candidates)-1
        index = 0
        for _ in xrange(aggression):
            index = random.randint(index, max_index)
        if index >= max_index-1 and max_index >= 1:
            index = random.choice([max_index, max_index-1])
        chosen = candidates[index]

        rank = [i for i in self.location_ranks
                if chosen in self.location_ranks[i]]
        assert len(rank) == 1
        rank = rank[0]
        #print item, chosen, rank, max_rank, index, max_index, aggression
        self.assign_item_location(item, chosen)

    def assign_item_location(self, item, location):
        #print "-", item, location
        new_locations = self.get_item_unlocked_locations(item)
        max_rank = max(self.location_ranks)
        self.assignments[location] = item
        if new_locations:
            self.location_ranks[max_rank+1] = new_locations

    def unassign_item(self, item):
        location = self.get_assigned_location(item)
        del(self.assignments[location])
        assert self.get_assigned_location(item) is None

    def get_location_rank(self, location):
        for i in sorted(self.location_ranks):
            if location in self.location_ranks[i]:
                return i
        return None

    def get_item_rank(self, item):
        location = self.get_assigned_location(item)
        return self.get_location_rank(location)

    def choose_item(self, aggression=3):
        if hasattr(self, "item_set_in_progress") and self.item_set_in_progress:
            chosen = random.choice(self.item_set_in_progress)
            self.item_set_in_progress.remove(chosen)
            return chosen

        requirements = sorted([r for r in self.ranked_requirements
                               if r not in self.assigned_items
                               and r not in self.custom_assignments.values()])
        unlocked = {}
        for r in requirements:
            unlocked[r] = self.get_item_unlocked_locations(r)
        candidates = [r for r in requirements if len(unlocked[r]) > 0]

        unused = [r for r in requirements if r not in candidates]
        unused_unlocked = self.get_item_unlocked_locations(unused)
        if unused_unlocked:
            random.shuffle(unused)
            for u in list(unused):
                if u not in unused:
                    continue
                unused.remove(u)
                temp = self.get_item_unlocked_locations(unused)
                if temp:
                    failure = False
                    for key in unlocked:
                        if (set(unlocked[key]) >= set(temp) or
                                (unlocked[key]
                                 and set(unlocked[key]) <= set(temp))):
                            failure = True
                            break
                    if failure:
                        unused = []
                        break
                if not temp:
                    unused.append(u)
            if unused:
                key = tuple(sorted(unused))
                unlocked[key] = self.get_item_unlocked_locations(key)
                candidates.append(key)

        if not candidates:
            return None

        chosen = random.choice(candidates)
        if len(unlocked[chosen]) > 0:
            candidates = [r for r in requirements
                          if unlocked[r]
                          and unlocked[r] < unlocked[chosen]
                          and r not in self.assigned_items]
            if len(candidates) > 0:
                while True:
                    candidates = [c for c in candidates
                                  if unlocked[c]
                                  and unlocked[c] < unlocked[chosen]
                                  and c not in self.assigned_items]
                    if not candidates:
                        break
                    c = random.choice(candidates)
                    ratio = len(unlocked[c]) / float(len(unlocked[chosen]))
                    ratio = ratio ** aggression
                    if random.random() > ratio:
                        chosen = c
                    candidates.remove(c)

        if not isinstance(chosen, basestring):
            self.item_set_in_progress = sorted(chosen)
            return self.choose_item(aggression=aggression)

        return chosen

    def assign_everything(self, aggression=3):
        if not hasattr(self, "custom_assignments"):
            self.custom_assignments = {}
        if not hasattr(self, "location_ranks"):
            self.location_ranks = defaultdict(set)
            self.location_ranks[0] = self.assignable_locations
        while True:
            if self.check_custom():
                continue
            item = self.choose_item(aggression=aggression)
            if item is None:
                break
            assert item not in self.assigned_items
            self.assign_item(item, aggression=aggression)
            assert item in self.assigned_items
        self.force_custom()

    def clear_assignments(self):
        delattr(self, "location_ranks")
        self.assignments = {}

    def set_custom_assignments(self, custom_assignments):
        self.custom_assignments = dict(custom_assignments)

    @property
    def unassigned_custom_assignments(self):
        return sorted([(k, v) for (k, v) in self.custom_assignments.items()
                       if k not in self.assignments])

    def check_custom(self):
        locations = self.custom_assignments.keys()
        locations = set(locations) & set(self.assignable_locations)
        for l in locations:
            self.assign_item_location(self.custom_assignments[l], l)
            del(self.custom_assignments[l])
        if locations:
            return True
        return False

    def force_custom(self):
        for l, item in self.unassigned_custom_assignments:
            self.assignments[l] = item
            del(self.custom_assignments[l])
