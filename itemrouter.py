from randomtools.utils import utilrandom as random
from collections import defaultdict

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

    def check_assignable(self, label):
        if (not hasattr(self, "_previous_assigned") or
                self._previous_assigned != self.assigned_items):
            self._previous_assigned = self.assigned_items
            self._assignable_cache = {}
        elif label in self._assignable_cache:
            return self._assignable_cache[label]
        conditions = self.assign_conditions[label]
        if conditions == '*':
            return True
        for or_cond in conditions.split('|'):
            for and_cond in or_cond.split('&'):
                if and_cond in self.definitions:
                    truth = self.check_assignable(and_cond)
                else:
                    truth = and_cond in self.assigned_items
                if not truth:
                    break
            else:
                self._assignable_cache[label] = True
                return self.check_assignable(label)
        self._assignable_cache[label] = False
        return self.check_assignable(label)

    def get_total_requirements(self, label, cached=True):
        requirements = set([])
        conditions = self.assign_conditions[label]
        if conditions == '*':
            return set([])
        for or_cond in conditions.split('|'):
            for and_cond in or_cond.split('&'):
                if and_cond in self.definitions:
                    if cached:
                        requirements |= self.get_requirements(and_cond)
                    else:
                        requirements |= self.get_total_requirements(
                            and_cond, cached=False)
                else:
                    requirements.add(and_cond)
        return requirements

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

    def get_item_unlocked_locations(self, item):
        baseline_locations = self.assignable_locations
        self.assignments[None] = item
        unlocked_locations = self.assignable_locations - baseline_locations
        del(self.assignments[None])
        return unlocked_locations

    @property
    def unreachable_locations(self):
        return set([
            k for k in self.assign_conditions if
            k not in self.assignable_locations and
            k not in self.assigned_locations and
            k not in self.definitions])

    def assign_item(self, item, aggression=3):
        assignable_locations = self.assignable_locations
        if not hasattr(self, "location_ranks"):
            self.location_ranks = defaultdict(set)
            self.location_ranks[0] = assignable_locations
        if not assignable_locations:
            raise Exception("No assignable locations.")

        new_locations = self.get_item_unlocked_locations(item)
        if not new_locations:
            aggression = max(aggression-1, 1)

        max_rank = max(self.location_ranks)
        candidates = []
        for i in xrange(max_rank+1):
            temp = sorted(self.location_ranks[i] & assignable_locations)
            random.shuffle(temp)
            candidates += temp

        max_index = len(candidates)-1
        index = 0
        for _ in xrange(aggression):
            index = random.randint(index, max_index)
        chosen = candidates[index]
        rank = [i for i in self.location_ranks
                if chosen in self.location_ranks[i]]
        assert len(rank) == 1
        rank = rank[0]

        self.assignments[chosen] = item
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

    def choose_item(self, aggression=3):
        requirements = sorted([r for r in self.ranked_requirements
                               if r not in self.assigned_items])
        unlocked = {}
        for r in requirements:
            unlocked[r] = self.get_item_unlocked_locations(r)
        candidates = [r for r in requirements if len(unlocked[r]) > 0]
        if not candidates:
            candidates = requirements
        if not candidates:
            return None
        chosen = random.choice(candidates)
        if len(unlocked[chosen]) > 0:
            candidates = [r for r in requirements
                          if unlocked[r]
                          and unlocked[r] <= unlocked[chosen]
                          and r not in self.assigned_items]
            if len(candidates) > 1:
                candidates = sorted(
                    candidates,
                    key=lambda r: (len(unlocked[r]), random.random(), r))
                max_index = len(candidates)-1
                index = max_index
                for _ in xrange(max(aggression-1, 1)):
                    index = random.randint(0, index)
                chosen = candidates[index]
        return chosen

    def assign_everything(self, aggression=3):
        while True:
            item = self.choose_item(aggression=aggression)
            if item is None:
                break
            assert item not in self.assigned_items
            self.assign_item(item, aggression=aggression)
            assert item in self.assigned_items

    def clear_assignments(self):
        delattr(self, "location_ranks")
        self.assignments = {}
