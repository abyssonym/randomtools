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
    def useful_ranked_requirements(self):
        requirements = self.ranked_requirements
        num_locations_baseline = len(self.assignable_locations)
        useful = []
        for req in requirements:
            self.assignments[None] = req
            if len(self.assignable_locations) > num_locations_baseline:
                useful.append(req)
        if None in self.assignments:
            del(self.assignments[None])
        return useful

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

    @property
    def unreachable_locations(self):
        return set([
            k for k in self.assign_conditions if
            k not in self.assignable_locations and
            k not in self.assigned_locations and
            k not in self.definitions])

    def assign_item(self, item, relaxed=False):
        assignable_locations = self.assignable_locations
        if not hasattr(self, "location_ranks"):
            self.location_ranks = defaultdict(set)
            self.location_ranks[0] = assignable_locations
        if not assignable_locations:
            raise Exception("No assignable locations.")
        max_rank = max(self.location_ranks)
        while True:
            rank = random.randint(random.randint(0, max_rank), max_rank)
            if not relaxed:
                rank = random.randint(rank, max_rank)
            candidates = assignable_locations & self.location_ranks[rank]
            if candidates:
                break
        chosen = random.choice(sorted(candidates))
        self.assignments[chosen] = item
        new_locations = self.assignable_locations - assignable_locations
        if len(new_locations) <= 1:
            self.location_ranks[max_rank] |= new_locations
        else:
            self.location_ranks[max_rank+1] = new_locations

    def get_location_rank(self, location):
        for i in sorted(self.location_ranks):
            if location in self.location_ranks[i]:
                return i
        return None

    def choose_item(self):
        requirements = self.useful_ranked_requirements
        if not requirements:
            requirements = self.ranked_requirements
        if not requirements:
            return None
        max_index = len(requirements)-1
        index = random.randint(0, random.randint(0, max_index))
        return requirements[index]

    def assign_everything(self):
        while True:
            item = self.choose_item()
            if item is None:
                break
            self.assign_item(item)

    def clear_assignments(self):
        delattr(self, "location_ranks")
        self.assignments = {}
