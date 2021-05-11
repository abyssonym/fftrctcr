from randomtools.tablereader import (
    TableObject, addresses, names, get_activated_patches, get_open_file,
    mutate_normal, get_seed, get_global_label, tblpath,
    get_random_degree, get_difficulty, write_patch,
    SANDBOX_PATH)
from randomtools.utils import (
    classproperty, cached_property, utilrandom as random)
from randomtools.interface import (
    run_interface, clean_and_write, finish_interface,
    get_activated_codes, get_flags, get_outfile,
    write_cue_file)

from collections import Counter, defaultdict
from hashlib import md5
from math import ceil
from os import path, walk
from sys import argv
from traceback import format_exc

import re


VERSION = '1'
ALL_OBJECTS = None

def lange(*args):
    return list(range(*args))


class MutateBoostMixin(TableObject):
    def mutate(self):
        super().mutate()
        for attr in self.mutate_attributes:
            minval, maxval = self.mutate_attributes[attr]
            value = getattr(self, attr)
            if minval <= value <= maxval:
                while random.random() < self.random_degree ** 2.5:
                    value += random.randint(-1, 1)
                    value = max(minval, min(maxval, value))
                    setattr(self, attr, value)


class AbilityObject(TableObject): pass


class AbilityAttributesObject(MutateBoostMixin):
    flag = 'a'
    flag_description = 'abilities'

    # Ry Edit: List of formulas that should be able to inflict status
    STATUS_FORMULAS = [1, 8, 9, 0xa, 0xb, 0xd, 0xe, 0x1e, 0x1f, 0x20, 0x21,
                       0x22, 0x24, 0x26, 0x28, 0x29, 0x2d, 0x31, 0x33, 0x35,
                       0x38, 0x3d, 0x3f, 0x40, 0x41, 0x47, 0x4e, 0x50, 0x51,
                       0x52, 0x53, 0x57, 0x5a, 0x5b, 0x5e, 0x5f, 0x60]

    mutate_attributes = {
        'ct': (1, 0xfd),
        'mp': (1, 0xfd),
        'xval': (1, 0xfd),
        'yval': (1, 0xfd),
        'range': (0, 0x10),
        'effect': (0, 0x10),
        'vertical': (0, 0x10),
        }

    def mutate_status(self):
        # Ry Edit: Ability Inflict Status randomizer
        random_degree = AbilityStatusObject.random_degree
        if self.index == 0x1d:
            # Excluding Frog, because I feel like there's some hardcoding for
            # the AI's usage of it
            return

        formula = self.formula
        value = self.inflict_status
        if (value > 0) or (formula in self.STATUS_FORMULAS):
            if random.random() < random_degree ** 1.15:
                if value > 0 and random.random() > random_degree ** 1.65:
                    # 2% Chance for a pre-existing Inflict Status to be
                    # randomized; 20% otherwise
                    return
                inflictstatus = random.choice(InflictStatusObject.every)
                if inflictstatus.is_crystallize:
                    # Banning Crystal if it'd hit more than 1 unit
                    effectarea = self.effect
                    if (effectarea > 0 or self.get_bit("math_skill")
                            or self.get_bit("3_directions")):
                        return
                    # Add code here to ensure that all Ramza classes and Rafa
                    # are immune to Crystal?

                self.inflict_status = inflictstatus.index
                ability = AbilityObject.get(self.index)
                if (ability.get_bit("add_status")
                        or ability.get_bit("cancel_status")):
                    # Correcting the AI flags if ability normally does status
                    if inflictstatus.get_bit("cancel"):
                        ability.set_bit("add_status", False)
                        ability.set_bit("cancel_status", True)
                    elif (inflictstatus.get_bit("separate") or
                            inflictstatus.get_bit("random") or
                            inflictstatus.get_bit("all_or_nothing")):
                        ability.set_bit("add_status", True)
                        ability.set_bit("cancel_status", False)

    def cleanup(self):
        if self.range == 0 and self.old_data['range'] != 0:
            self.range = self.old_data['range']


class AbilityStatusObject(TableObject):
    flag = 'y'
    flag_description = 'ability/weapon status effects and procs'

    def mutate(self):
        AbilityAttributesObject.get(self.index).mutate_status()


class JobObject(TableObject):
    GENERIC_NAMES = [
        "squire", "chemist", "knight", "archer", "monk", "priest", "wizard",
        "timemage", "summoner", "thief", "mediator", "oracle", "geomancer",
        "lancer", "samurai", "ninja", "calculator", "bard", "dancer", "mime",
        ]

    VALID_INNATE_STATUSES = 0xcafce12a10
    VALID_START_STATUSES = (VALID_INNATE_STATUSES |
                            0x1402100000)
    BENEFICIAL_STATUSES =   0xc278600000
    RERAISE_STATUS =        0x0000200000
    FAITH_STATUS =          0x8000000000
    INNOCENT_STATUS =       0x4000000000
    INVITE_STATUS =         0x0000004000

    BANNED_RSMS = [0x1bb, 0x1d7, 0x1e1, 0x1e4, 0x1e5, 0x1f1]
    MP_RESTORE_INNATES = [0x1ee, 0x1b6, 0x1b0]
    LUCAVI_INNATES = (lange(0x1a6, 0x1a9) + [0x1aa] + lange(0x1ac, 0x1b0)
                      + lange(0x1b1, 0x1b4) + [0x1b5, 0x1ba, 0x1bd, 0x1be]
                      + lange(0x1c0, 0x1c6)
                      + lange(0x1d1, 0x1d6) + [0x1d8, 0x1dd, 0x1e3]
                      + [0x1e7, 0x1e8]
                      + lange(0x1eb, 0x1ee) + [0x1f2, 0x1f3, 0x1fa, 0x1fb]
                      ) + MP_RESTORE_INNATES

    LUCAVI_ORDER = [0x43, 0x3c, 0x3e, 0x45, 0x40, 0x41, 0x97, 0x49]
    MONSTER_JOBS = lange(0x5e, 0x8e) + [0x90, 0x91, 0x96, 0x97, 0x99, 0x9a]
    STORYLINE_RECRUITABLE_NAMES = {
        'Ramza', 'Mustadio', 'Agrias', 'Meliadoul', 'Rafa', 'Malak', 'Orlandu',
        'Beowulf', 'Cloud', 'Reis',
        }

    GROUP_RECRUITABLE = 1
    GROUP_LUCAVI = 2
    GROUP_MONSTER = 3
    GROUP_SPECIAL = 4

    randomselect_attributes = [
        ('hpgrowth', 'hpmult'),
        ('mpgrowth', 'mpmult'),
        ('spdgrowth', 'spdmult'),
        ('pagrowth', 'pamult'),
        ('magrowth', 'mamult'),
        'move', 'jump', 'evade',
        ]

    mutate_attributes = {}
    for key in randomselect_attributes:
        if isinstance(key, str):
            key = [key]
        for attr in key:
            if attr not in mutate_attributes:
                mutate_attributes[attr] = None

    magic_mutate_bit_attributes = {
        ('equips',): (0xffffffff,),
        ('innate_status', 'immune_status', 'start_status'):
            (VALID_START_STATUSES,)*3,
        ('absorb_elem', 'nullify_elem', 'resist_elem', 'weak_elem'): (0xff,)*4,
        }

    @classproperty
    def character_jobs(self):
        if hasattr(JobObject, '_character_jobs'):
            return JobObject._character_jobs

        character_jobs = defaultdict(set)
        for u in UnitObject.every:
            if u.entd >= 0x1db:
                continue
            if 'NO-NAME' not in u.character_name:
                character_jobs[u.character_name].add(u.old_data['job'])

        JobObject._character_jobs = {}
        for name in character_jobs:
            JobObject._character_jobs[name] = [
                JobObject.get(j) for j in sorted(character_jobs[name])
                if JobObject.get(j).is_special]

        return JobObject.character_jobs

    @cached_property
    def character_name(self):
        names = [n for n in self.character_jobs
                 if self in self.character_jobs[n]]
        if not names:
            return 'NONE'
        if len(names) == 2 and 'RANDOM GENERIC' in names:
            names.remove('RANDOM GENERIC')
        return ','.join(sorted(names))

    @cached_property
    def relatives(self):
        if self.character_name in ['NONE', 'RANDOM GENERIC']:
            return [self]
        relatives = [j for j in JobObject.every
                     if j.character_name == self.character_name]
        relatives = sorted(relatives, key=lambda r: (r.signature, r.index))
        return relatives

    @cached_property
    def canonical_relative(self):
        if self.character_name in ['NONE', 'RANDOM GENERIC']:
            return self
        return self.relatives[0]

    @property
    def is_canonical(self):
        return self.canonical_relative is self

    @property
    def is_generic(self):
        return 0x4a <= self.index <= 0x5d

    @property
    def is_monster(self):
        return self.index >= 0x5e and self.index != 0x97

    @property
    def is_lucavi(self):
        return self.index in self.LUCAVI_ORDER

    @property
    def is_special(self):
        return 1 <= self.index <= 0x49 or self.index == 0x97

    @property
    def intershuffle_group(self):
        if self.is_generic or (self.is_canonical and self.character_name in
                               self.STORYLINE_RECRUITABLE_NAMES):
            return self.GROUP_RECRUITABLE
        if self.is_lucavi:
            return self.GROUP_LUCAVI
        if self.is_monster:
            return self.GROUP_MONSTER
        if self.intershuffle_valid:
            return self.GROUP_SPECIAL
        return -1

    @property
    def intershuffle_valid(self):
        for attr in self.mutate_attributes:
            if self.old_data[attr] == 0:
                return False
        return True

    @property
    def rank(self):
        if self.intershuffle_group == self.GROUP_RECRUITABLE:
            return 1

        if self.intershuffle_group == self.GROUP_LUCAVI:
            return 1

        if hasattr(self, '_rank'):
            return self._rank

        rank_attrs = set()
        for attr in self.mutate_attributes:
            rank_attr = '_%s_rank' % attr
            rank_attrs.add(rank_attr)
            reverse = attr.endswith('growth')
            ranked = sorted(
                JobObject.every, key=lambda j: (j.old_data[attr],
                                                j.signature,
                                                j.index), reverse=reverse)
            max_index = len(ranked)-1
            for i, j in enumerate(ranked):
                setattr(j, rank_attr, i / max_index)

        for j in JobObject.every:
            ranks = [getattr(j, attr) for attr in sorted(rank_attrs)]
            ranks.append(1 if j.is_lucavi else 0)
            j._rank = sum(ranks) / len(ranks)

        return self.rank

    @property
    def name(self):
        if self.is_generic:
            return self.GENERIC_NAMES[self.index-0x4a].upper()
        else:
            return 'JOB {0:0>2X}'.format(self.index)

    def magic_mutate_bits(self):
        super().magic_mutate_bits(random_degree=self.random_degree ** 0.5)

    def preprocess(self):
        for attr in self.old_data:
            if attr.endswith('growth') and self.old_data[attr] == 0:
                setattr(self, attr, 0xff)
                self.old_data[attr] = 0xff

    def preclean(self):
        if len(self.relatives) > 1:
            for r in self.relatives:
                my_equips = self.old_data['equips']
                their_equips = r.old_data['equips']
                if (my_equips & their_equips == their_equips and
                        self.equips & r.equips != r.equips):
                    if random.choice([True, False]):
                        self.equips |= r.equips
                    else:
                        r.equips &= self.equips
                    assert self.equips & r.equips == r.equips

    def cleanup(self):
        if not self.is_canonical:
            canonical = self.canonical_relative
            for attr in self.old_data:
                if self.old_data[attr] == canonical.old_data[attr]:
                    setattr(self, attr, getattr(canonical, attr))

        if self.is_lucavi:
            self.start_status &= self.BENEFICIAL_STATUSES
            self.innate_status &= self.BENEFICIAL_STATUSES
        self.innate_status ^= (self.innate_status & self.immune_status)
        self.start_status ^= (self.start_status & self.immune_status)
        self.start_status |= self.innate_status

        innate_changes = (self.innate_status & (
            self.innate_status ^ self.old_data['innate_status']))
        invalid_innate = innate_changes & (
            innate_changes ^ self.VALID_INNATE_STATUSES)
        self.innate_status ^= invalid_innate

        start_changes = (self.start_status & (
            self.start_status ^ self.old_data['start_status']))
        invalid_start = start_changes & (
            start_changes ^ self.VALID_START_STATUSES)
        self.start_status ^= invalid_start

        if self.is_lucavi and get_difficulty() >= 1.0:
            for attr in self.mutate_attributes:
                value = getattr(self, attr)
                if attr.endswith('growth'):
                    setattr(self, attr, min(value, self.old_data[attr]))
                else:
                    setattr(self, attr, max(value, self.old_data[attr]))


class ItemObject(MutateBoostMixin):
    flag = 'p'
    flag_description = 'shop item availability'

    BANNED_ITEMS = [0x49]
    PRICELESS_ITEMS = [0x6a, 0x8f]

    mutate_attributes = {
        'price': (0, 65000),
        'time_available': (1, 16),
        'enemy_level': (1, 99),
        }

    @property
    def rank(self):
        if self.index == 0:
            return -1

        rank = self.old_data['price']
        if self.priceless:
            rank += 65000
            rank += (self.old_data['enemy_level'] * 100)
        return rank

    @property
    def priceless(self):
        if self.price <= 10:
            return True
        elif self.index in self.PRICELESS_ITEMS:
            return True

    def mutate_item_attributes(self):
        # Ry Edit: Item Attribute Randomizer
        random_degree = ItemAttributesObject.random_degree
        if (self.index > 0 and self.attributes == 0
                and random.random() < random_degree ** 1.65):
            newattributes = random.choice(
                [i for i in ItemAttributesObject.every if i.is_new])
            self.attributes = newattributes.index

    def preprocess(self):
        if self.flag in get_flags():
            if (self.get_bit("rare")
                    and random.random() < self.random_degree ** 0.2):
                if (self.index in self.BANNED_ITEMS
                        and random.random() > self.random_degree ** 0.75):
                    pass
                else:
                    if self.enemy_level <= 5:
                        self.enemy_level = 50
                    self.set_bit("rare", False)

        if ItemAttributesObject.flag in get_flags():
            self.reseed('attributes')
            self.mutate_item_attributes()

    def cleanup(self):
        self.price = int(round(self.price, -1))
        if self.price > 500:
            self.price = int(round(self.price, -2))


class WeaponObject(MutateBoostMixin):
    flag = 'w'

    mutate_attributes = {
        'range': None,
        'weapon_power': None,
        'evade': None,
        }

    def mutate_proc(self):
        random_degree = WeaponStatusObject.random_degree
        value = self.inflict_status
        if (self.formula == 1 and value == 0
                and random.random() < random_degree ** 1.15):
            # 20% chance to turn a non-status Formula 1 move into Formula 2
            self.formula = 2
            self.inflict_status = 0

        if self.formula == 2:
            # Formula 2 calls the "inflict status" value
            # as a spell to cast 25% of the time
            if value == 0 or random.random() < random_degree ** 1.65:
                # 10% chance for pre-existing spell casts to be randomized
                # Value is capped at FF internally, so no abilities
                # past Holy Bracelet
                newvalue = random.randint(1, 0xff)
                if newvalue in [0x28, 0x2d, 0xb8, 0xdb, 0xdc]:
                    # Empty abilities
                    newvalue = random.randint(1, 0x1f)
                self.inflict_status = newvalue

    def mutate_status(self):
        random_degree = WeaponStatusObject.random_degree
        if self.formula != 2 and random.random() < random_degree ** 1.65:
            value = self.inflict_status
            if value > 0 and random.random() > random_degree ** 1.65:
                # 1% Chance for a pre-existing Inflict Status to be randomized
                # 10% otherwise
                return
            inflictstatus = random.choice(InflictStatusObject.every)
            if inflictstatus.is_crystallize:
                # Banning Crystal (since it's more likely to appear on weapons)
                return
            self.inflict_status = inflictstatus.index

    def cleanup(self):
        if self.range == 0 and self.old_data['range'] != 0:
            self.range = self.old_data['range']


class WeaponStatusObject(TableObject):
    flag = 'y'

    def mutate(self):
        if random.choice([True, False]):
            WeaponObject.get(self.index).mutate_status()
            WeaponObject.get(self.index).mutate_proc()
        else:
            WeaponObject.get(self.index).mutate_proc()
            WeaponObject.get(self.index).mutate_status()


class ShieldObject(TableObject):
    flag = 'w'

    mutate_attributes = {
        'physical_evade': (0, 0x50),
        'magic_evade': (0, 0x50),
        }

class ArmorObject(TableObject):
    flag = 'w'

    mutate_attributes = {
        'hp_bonus': (0, 0xfd),
        'mp_bonus': (0, 0xfd),
        }

class AccessoryObject(TableObject):
    flag = 'w'

    mutate_attributes = {
        'physical_evade': (0, 0x3c),
        'magic_evade': (0, 0x3c),
        }

class ChemistItemObject(TableObject):
    flag = 'w'

    mutate_attributes = {
        'zval': (1, 0xfd),
        }


class InflictStatusObject(TableObject):
    flag = 'y'

    @property
    def is_crystallize(self):
        return self.index == 0x60

    # TODO: randomize_empty
    @property
    def is_empty(self):
        return (0x1D <= self.index <= 0x1F) or (0x7A <= self.index <= 0x7F)

    def randomize(self):
        if self.is_empty:
            toinflict = 0
            while True:
                bit = (1 << random.randint(0, 39))
                if not bit & JobObject.VALID_START_STATUSES:
                    continue
                toinflict |= bit
                if (toinflict and
                        random.randint(1, 2**(bin(toinflict).count("1"))) > 1):
                    break
            self.statuses_to_inflict = toinflict
            if not (self.statuses_to_inflict == 0x0000000000):
                choice = random.randint(1, 9)
                if choice <= 3: # 33%
                    self.set_bit("random", True)
                elif choice <= 6: # 33%
                    self.set_bit("separate", True)
                elif choice <= 8: # 22%
                    self.set_bit("cancel", True)
                else: # 11%
                    self.set_bit("all_or_nothing", True)


class ItemAttributesObject(MutateBoostMixin):
    flag = 'w'
    flag_description = 'weapon and item stats'

    mutate_attributes = {
        'pa': (1, 0xfd),
        'ma': (1, 0xfd),
        'speed': (1, 0xfd),
        'move': (1, 0xfd),
        'jump': (1, 0xfd),
        }

    @property
    def is_new(self):
        return 0x4a <= self.index <= 0x4e

    def preprocess(self):
        if self.is_new and self.flag in get_flags():
            if self.index == 0x4a:
                # Static Item Attributes to be used to "mutate" weapons
                # that don't have Attributes normally
                self.pa = 1
            elif self.index == 0x4b:
                self.ma = 1
            elif self.index == 0x4c:
                self.speed = 1
            elif self.index == 0x4d:
                self.move = 1
            elif self.index == 0x4e:
                self.jump = 1


class SkillsetObject(TableObject):
    BANNED_SKILLS = lange(0x165, 0x16f)
    MATH_SKILLETS = {0xa, 0xb, 0xc, 0x10}
    BANNED_ANYTHING = {0x18}  # mimic
    BANNED_SKILLSET_SHUFFLE = {0, 1, 2, 3, 6, 8, 0x11, 0x12, 0x13, 0x14, 0x15,
                               0x18, 0x34, 0x38, 0x39, 0x3b, 0x3e, 0x9c, 0xa1
                               } | BANNED_ANYTHING

    @classproperty
    def character_skillsets(self):
        skillsets = {}
        for name in JobObject.character_jobs:
            jobs = JobObject.character_jobs[name]
            skillsets[name] = []
            for j in jobs:
                try:
                    ss = SkillsetObject.get(j.skillset)
                    skillsets[name].append(ss)
                except KeyError:
                    pass
        return skillsets

    def is_generic(self):
        return 5 <= self.index <= 0x18

    def get_actions(self, old=False):
        if old:
            actionbits = ((self.old_data['actionbits1'] << 8)
                           | self.old_data['actionbits2'])
            actionbytes = self.old_data['actionbytes']
        else:
            actionbits = (self.actionbits1 << 8) | self.actionbits2
            actionbytes = self.actionbytes
        actions = []
        for i, a in enumerate(actionbytes):
            if actionbits & (1 << (0xf-i)):
                a |= 0x100
            actions.append(a)
        return actions

    @property
    def actions(self):
        return self.get_actions()

    @property
    def old_actions(self):
        return self.get_actions(old=True)

    def set_actions(self, actions, order_new=False):
        assert 0 not in actions
        actions = sorted(actions)
        old_actions = [a for a in actions if a in self.old_actions]
        new_actions = [a for a in actions if a not in old_actions]
        if order_new:
            actions = new_actions + old_actions
        else:
            actions = old_actions + new_actions
        actionbits = 0
        actionbytes = []
        for i, a in enumerate(actions):
            if a & 0x100:
                actionbits |= (1 << (0xf-i))
            actionbytes.append(a & 0xff)
        self.actionbytes = actionbytes
        self.actionbits1 = actionbits >> 8
        self.actionbits2 = actionbits & 0xff

    @property
    def rsms(self):
        rsms = []
        for i, rsm in enumerate(self.rsmbytes):
            if self.rsmbits & (1 << (0x7-i)):
                rsm |= 0x100
            rsms.append(rsm)
        return rsms

    def set_rsms(self, rsms):
        assert 0 not in rsms
        rsms = sorted(rsms)
        rsmbits = 0
        rsmbytes = []
        for i, rsm in enumerate(rsms):
            if rsm & 0x100:
                rsmbits |= (1 << (0x7-i))
            rsmbytes.append(rsm & 0xff)
        self.rsmbytes = rsmbytes
        self.rsmbits = rsmbits

    @classmethod
    def intershuffle(self):
        rsms = set()
        rsm_count = 0
        job_actions = {}
        for name in JobObject.STORYLINE_RECRUITABLE_NAMES:
            skillsets = SkillsetObject.character_skillsets[name]
            actions = set()
            rsm_counts = []
            for ss in skillsets:
                rsms |= set(ss.rsms)
                rsm_counts.append(len([rsm for rsm in ss.rsms if rsm]))
                actions |= set(ss.actions)
            rsm_count += max(rsm_counts)
            actions -= {0}
            job_actions[name] = actions

        for ss in SkillsetObject.every:
            if ss.is_generic:
                rsms |= set(ss.rsms)
                rsm_count += len([rsm for rsm in ss.rsms if rsm])

        shuffled_names = sorted(job_actions)
        random.shuffle(shuffled_names)
        no_inherit_from = set()
        for i, name1 in enumerate(shuffled_names):
            for j, name2 in enumerate(shuffled_names):
                if j >= i:
                    continue
                if no_inherit_from & {name1, name2}:
                    continue
                actions1, actions2 = job_actions[name1], job_actions[name2]
                if actions1 < actions2 or actions2 < actions1:
                    no_inherit_from.add(random.choice((name1, name2)))

        shuffle_skillsets = sorted(job_actions)
        shuffle_skillsets += [
            ss.index for ss in SkillsetObject.every
            if ss.is_generic and ss.index not in self.BANNED_SKILLSET_SHUFFLE]
        inherit_from = [ss for ss in shuffle_skillsets
                        if ss not in no_inherit_from]
        while len(inherit_from) < len(shuffle_skillsets):
            inherit_from.append(random.choice(shuffle_skillsets))
        assert set(inherit_from) <= set(shuffle_skillsets)
        assert not set(shuffle_skillsets) & self.BANNED_SKILLSET_SHUFFLE
        random.shuffle(inherit_from)

        exchange_skills = {}
        for key in shuffle_skillsets:
            if key in job_actions:
                actions = job_actions[key]
            else:
                actions = SkillsetObject.get(key).actions
            actions = [a for a in sorted(actions) if a > 0]
            max_exchange = (
                len(actions) * (SkillsetObject.random_degree ** 0.5))
            num_exchange = int(round(
                random.uniform(random.uniform(0, max_exchange), max_exchange)))
            to_exchange = random.sample(actions, num_exchange)
            exchange_skills[key] = to_exchange

        final_actions = {}
        for base, inherit in zip(shuffle_skillsets, inherit_from):
            if base in job_actions:
                actions = job_actions[base]
            else:
                actions = SkillsetObject.get(base).actions
            actions = [a for a in actions if a not in exchange_skills[base]]
            actions += exchange_skills[inherit]
            actions = [a for a in sorted(set(actions)) if a > 0]
            if len(actions) > 16:
                actions = random.sample(actions, 16)
            final_actions[base] = actions

        rsms.add(0x1e3)
        rsms.add(0x1f3)
        rsms = [rsm for rsm in sorted(rsms) if rsm > 0]
        temp = list(rsms)
        while len(temp) < rsm_count:
            temp.append(random.choice(rsms))
        rsms = temp

        final_rsms = defaultdict(set)
        candidates = sorted([name for name in shuffle_skillsets
                             if isinstance(name, str)])
        candidates += [sso.index for sso in SkillsetObject.every
                       if sso.is_generic]
        for rsm in rsms:
            while True:
                chosen = random.choice(candidates)
                if len(final_rsms[chosen]) >= 6:
                    continue
                final_rsms[chosen].add(rsm)
                break

        done_skillsets = {}
        for name in sorted(SkillsetObject.character_skillsets):
            if name not in final_actions:
                continue
            skillsets = SkillsetObject.character_skillsets[name]
            order_new = random.choice([True, False])
            for ss in skillsets:
                if ss.index in self.BANNED_SKILLSET_SHUFFLE:
                    continue
                actions = final_actions[name]
                actions = [a for a in actions if a in ss.old_actions
                           or a not in job_actions[name]]
                ss.set_actions(actions, order_new)
                ss.set_rsms(final_rsms[name])
                if ss in done_skillsets:
                    assert done_skillsets[ss] == name
                else:
                    done_skillsets[ss] = name

        for ss in SkillsetObject.every:
            if ss.is_generic:
                if ss.index in final_actions:
                    order_new = random.choice([True, False])
                    ss.set_actions(final_actions[ss.index], order_new)
                ss.set_rsms(final_rsms[ss.index])

    def cleanup(self):
        while len(self.actionbytes) < len(self.old_data['actionbytes']):
            self.actionbytes.append(0)
        while len(self.rsmbytes) < len(self.old_data['rsmbytes']):
            self.rsmbytes.append(0)
        if self.actions:
            assert all(action <= 0x1a5 for action in self.actions)
        if self.rsms:
            assert all(rsm >= 0x1a6 for rsm in self.rsms if rsm > 0)


class MonsterSkillsObject(TableObject): pass


class PoachObject(TableObject):
    flag = 't'
    flag_description = 'trophies, poaches, move-find items'

    mutate_attributes = {
        'common': ItemObject,
        'rare': ItemObject,
        }


class JobReqObject(TableObject): pass
class JobJPReqObject(TableObject): pass


class MoveFindObject(TableObject):
    flag = 't'
    done_locations = {}

    @classproperty
    def after_order(self):
        return [MeshObject]

    @property
    def map_index(self):
        return self.index // 4

    @cached_property
    def map(self):
        return GNSObject.get_by_map_index(self.map_index)

    @property
    def x(self):
        return self.coordinates >> 4

    @property
    def y(self):
        return self.coordinates & 0xF

    @property
    def is_active(self):
        return self.old_data['misc1'] != 0

    @property
    def old_item_null(self):
        return self.get_bit('always_trap', old=True) or (
            self.old_data['common'] == self.old_data['rare'] == 0)

    def set_coordinates(self, x, y):
        self.coordinates = (x << 4) | y

    def mutate(self):
        if self.map is None:
            return

        if self.map_index not in MoveFindObject.done_locations:
            MoveFindObject.done_locations[self.map_index] = set()

        if random.random() < self.random_degree ** 0.5:
            valid_locations = self.map.get_tiles_compare_attribute(
                'bad', False)
            valid_locations = [l for l in valid_locations if l not in
                               MoveFindObject.done_locations[self.map_index]]
            new_location = random.choice(valid_locations)
            self.set_coordinates(*new_location)

        template = random.choice([mfo for mfo in MoveFindObject.every
                                  if mfo.is_active])
        self.misc1 = template.misc1
        if (not template.old_item_null and (
                self.old_item_null
                or random.random() < self.random_degree)):
            common, rare = (template.old_data['common'],
                            template.old_data['rare'])
        else:
            common, rare = self.common, self.rare
        self.common = ItemObject.get(common).get_similar(
            random_degree=self.random_degree).index
        self.rare = ItemObject.get(rare).get_similar(
            random_degree=self.random_degree).index


class FormationObject(TableObject):
    @property
    def facing(self):
        # values with 0 rotation
        # rotate counterclockwise with rotation
        # 0: west
        # 1: south
        # 2: east
        # 3: north
        return self.orientation >> 4

    @property
    def rotation(self):
        # North is greater Y, East is greater X
        # first == least significant
        # 0: first bit in SW corner
        # 1: first bit in SE corner
        # 2: first bit in NE corner
        # 3: first bit in NW corner
        return self.orientation & 0xf

    @property
    def encounters(self):
        return [e for e in EncounterObject.every if self in e.formations]

    @property
    def entd(self):
        entds = {e.entd for e in EncounterObject.every if self in e.formations}
        assert len(entds) <= 1
        if entds:
            return list(entds)[0]
        return None

    @property
    def map(self):
        return GNSObject.get_by_map_index(self.map_index)

    @property
    def is_unused(self):
        if hasattr(self, '_claimed') and self._claimed:
            return False
        return self.bitmap == 0 and self.map_index == 0

    @classmethod
    def get_unused(self):
        for f in FormationObject.every:
            if f.is_unused:
                f._claimed = True
                return f

    def pick_correct_orientation(self):
        margin_x = min(self.x, self.map.width - (self.x + 1))
        margin_y = min(self.y, self.map.length - (self.y + 1))
        if (margin_x > margin_y or
                (margin_x == margin_y and random.choice([True, False]))):
            if self.y < (self.map.length / 2):
                # face north
                value = 3
            else:
                # south
                value = 1
        else:
            if self.x < (self.map.width / 2):
                # east
                value = 2
            else:
                # west
                value = 0
        self.orientation = value

    def generate(self, map_index, num_characters):
        self.map_index = map_index
        self.num_characters = num_characters
        tiles = self.map.get_recommended_tiles()
        max_index = len(tiles)-1
        while True:
            index = random.randint(random.randint(0, max_index), max_index)
            x, y = tiles[index]
            if random.choice([True, False]):
                x = max(1, min(x, self.map.width-2))
            if random.choice([True, False]):
                y = max(1, min(y, self.map.length-2))
            i_low = random.randint(-1, 0) + random.randint(-1, 0)
            i_high = random.randint(0, 1) + random.randint(0, 1)
            j_low = random.randint(-1, 0) + random.randint(-1, 0)
            j_high = random.randint(0, 1) + random.randint(0, 1)
            window = [(i, j) for (i, j) in tiles
                      if x + i_low <= i <= x + i_high
                      and y + j_low <= j <= y + j_high]
            window = [self.map.primary_meshes[0].get_tile(*t) for t in window]
            zs = [t.z for t in window]
            z = random.choice(zs)
            root_tile = self.map.primary_meshes[0].get_tile(x, y)
            k_low, k_high = 0, 0
            while k_low > -2 and random.choice([True, False, False, False]):
                k_low -= 1
            while k_high < 2 and random.choice([True, False, False, False]):
                k_high += 1
            window = [t for t in window
                      if z - k_low <= t.z <= z + k_high]
            if len(window) > num_characters:
                break
            elif (len(window) == num_characters
                    and random.choice([True, False, False, False])):
                break

        self.x = root_tile.x
        self.y = root_tile.y
        bitmap = 0
        for t in window:
            i = t.x - self.x
            j = t.y - self.y
            i, j = i + 2, j + 2
            assert 0 <= i <= 4
            assert 0 <= j <= 4
            # yes, the bitmap is indexed vertically
            index = (i * 5) + j
            bitmap |= (1 << index)
            self.map.set_party(t.x, t.y)

        self.bitmap = bitmap
        self.orientation = 0
        self.pick_correct_orientation()

    def preprocess(self):
        if (self.index == 0xe8 and self.map_index == 0x74
                and self.entd == 0x1cc):
            assert all(e.map_index == 0x32 for e in self.encounters)
            self.map_index = 0x32
            self.old_data['map_index'] = 0x32

    def cleanup(self):
        if self.encounters:
            assert {self.map_index} == {e.map_index for e in self.encounters}


class EncounterObject(TableObject):
    MAP_MOVEMENTS_FILENAME = path.join(tblpath, 'map_movements.txt')
    map_movements = defaultdict(list)
    for line in open(MAP_MOVEMENTS_FILENAME):
        map_index, data = line.split()
        map_index = int(map_index, 0x10)
        unit, x, y = data.split(',')
        unit = int(unit, 0x10)
        x, y = int(x), int(y)
        map_movements[map_index].append((unit, x, y))

    @classproperty
    def after_order(self):
        return [GNSObject]

    @cached_property
    def canonical_relative(self):
        if self.old_data['entd'] == 0:
            return self
        for e in EncounterObject.every:
            if e.old_data['entd'] == self.old_data['entd']:
                return e

    @property
    def is_canonical(self):
        return self.canonical_relative is self

    @property
    def units(self):
        return [u for u in UnitObject.every if u.entd == self.entd]

    @property
    def map(self):
        return GNSObject.get_by_map_index(self.map_index)

    @property
    def movements(self):
        return self.map_movements[self.map_index]

    @property
    def formations(self):
        return [FormationObject.get(f) for f in self.formation_indexes if f]

    @property
    def old_formations(self):
        return [FormationObject.get(f) for f in
                self.old_data['formation_indexes'] if f]

    def set_formations(self, f1, f2=0):
        f1 = f1.index
        f2 = f2.index if f2 else f2
        self.formation_indexes = [f1, f2]

    def set_occupied(self):
        for u, x, y in self.movements:
            self.map.set_occupied(x, y)

    def preprocess(self):
        self.set_occupied()
        if self.index == 0x1b2 and self.formation_indexes == [232, 324]:
            self.formation_indexes = [323, 324]
            self.old_data['formation_indexes'] = self.formation_indexes

    def generate_formations(self):
        # two cases: enemy locations randomized & not
        # problem: duplicate encounter objects / canonical
        templates = [e for e in EncounterObject.every if e.formations]
        template = random.choice(templates)
        num_formations = len(template.old_formations)
        num_characters = sum([f.num_characters for f in self.old_formations])
        if num_characters == 0:
            return
        assert 1 <= num_formations <= 2
        if num_formations == 2:
            numchars = [f.num_characters for f in template.old_formations]
            random.shuffle(numchars)
            ratio = numchars[0] / sum(numchars)
            n1 = int(round(num_characters * ratio))
            n2 = num_characters - n1
            assert 1 <= n1 < num_characters
            assert 1 <= n2 < num_characters
            assert n1 + n2 == num_characters
            f1 = FormationObject.get_unused()
            f1.generate(self.map_index, n1)
            f2 = FormationObject.get_unused()
            f2.generate(self.map_index, n2)
            self.set_formations(f1, f2)
        else:
            f = FormationObject.get_unused()
            f.generate(self.map_index, num_characters)
            self.set_formations(f)

        # do this after creating new units?
        units = list(self.units)
        random.shuffle(units)
        for u in units:
            if u.get_bit('randomly_present') or u.get_bit('always_present'):
                u.find_appropriate_position()

        print('ENTD {0:0>3X}'.format(self.entd))

    def randomize(self):
        if self.old_data['entd'] == 0:
            return
        if self.is_canonical:
            self.generate_formations()

    def cleanup(self):
        for attr in self.old_data:
            if self.old_data[attr] == self.canonical_relative.old_data[attr]:
                setattr(self, attr, getattr(self.canonical_relative, attr))

        for f in self.formations:
            assert f.map_index == self.map_index


class MapMixin(TableObject):
    @property
    def map_index(self):
        filename = path.split(self.filename)[-1]
        base, extension = filename.split('.')
        return int(base[-3:])

    @classmethod
    def get_by_map_index(self, map_index):
        result = [m for m in self.every if m.map_index == map_index]
        if len(result) == 1:
            return result[0]

    @classmethod
    def get_all_by_map_index(self, map_index):
        return [m for m in self.every if m.map_index == map_index]

    def read_data(self, filename=None, pointer=None):
        f = get_open_file(self.filename)
        self.data = f.read()

    def load_data(self, filename):
        f = get_open_file(filename)
        data = f.read()
        if data == self.data:
            print('WARNING: {0} contains unmodified data.'.format(filename))
        else:
            self.data = data
            if hasattr(self, '_property_cache'):
                del(self._property_cache)
            self._loaded_from = filename

        for e in EncounterObject.every:
            if e.map_index == self.map_index:
                e.set_occupied()

    def write_data(self, filename=None, pointer=None):
        f = get_open_file(self.filename)
        f.write(self.data)


class GNSObject(MapMixin):
    flag = 'q'
    flag_description = 'custom maps'

    CUSTOM_MAP_PATH = path.join('custom', 'maps')
    CUSTOM_INDEX_OPTIONS = {}

    filename_matcher = re.compile('^MAP(\d\d\d)\.(GNS|(\d+))')
    for parent, children, filenames in sorted(walk(CUSTOM_MAP_PATH)):
        indexes = set()
        filepaths = set()
        for f in filenames:
            match = filename_matcher.match(f)
            if match:
                indexes.add(match.group(1))
                filepaths.add(path.join(parent, f))
        if len(indexes) == 1:
            index = int(list(indexes)[0])
            if index not in CUSTOM_INDEX_OPTIONS:
                CUSTOM_INDEX_OPTIONS[index] = [None]
            CUSTOM_INDEX_OPTIONS[index].append(sorted(filepaths))

    @cached_property
    def meshes(self):
        return MeshObject.get_all_by_map_index(self.map_index)

    @property
    def primary_meshes(self):
        return [m for m in self.meshes if m.tiles]

    @property
    def width(self):
        widths = {m.width for m in self.primary_meshes}
        return max(widths)

    @property
    def length(self):
        lengths = {m.length for m in self.primary_meshes}
        return max(lengths)

    def randomize(self):
        if self.map_index not in self.CUSTOM_INDEX_OPTIONS:
            return

        options = self.CUSTOM_INDEX_OPTIONS[self.map_index]
        if 'novanilla' in get_activated_codes():
            options = [o for o in options if o is not None]

        chosen = random.choice(options)
        if chosen is None:
            return

        filenames = [path.split(fp)[1] for fp in chosen]
        file_map = dict(zip(filenames, chosen))
        done_filenames = set()
        for o in GNSObject.every + MeshObject.every + TextureObject.every:
            assert o.filename[:len(SANDBOX_PATH)] == SANDBOX_PATH
            _, filename = path.split(o.filename)
            if filename in file_map:
                load_filename = file_map[filename]
                o.load_data(load_filename)
                done_filenames.add(load_filename)

        unused = set(chosen) - done_filenames
        if unused:
            raise Exception(
                'Unused files: {0}'.format(' '.join(sorted(unused))))

    def get_tiles_compare_attribute(self, attribute, value,
                                    upper=False, compare_function=None):
        if compare_function is None:
            compare_function = lambda a, b: a == b
        width = min(m.width for m in self.primary_meshes)
        length = min(m.length for m in self.primary_meshes)
        coordinates = set()
        for y in range(length):
            for x in range(width):
                values = {getattr(m.get_tile(x, y, upper=upper), attribute)
                          for m in self.primary_meshes
                          if x < m.width and y < m.length}
                if all(compare_function(v, value) for v in values):
                    coordinates.add((x, y))
        return sorted(coordinates)

    def get_tile_attribute(self, x, y, attribute, upper=False):
        values = {getattr(m.get_tile(x, y, upper=upper), attribute)
                  for m in self.primary_meshes if x < m.width and y < m.length}
        if len(values) == 1:
            return list(values)[0]
        return values

    def set_occupied(self, x, y):
        for m in self.primary_meshes:
            try:
                t = m.get_tile(x, y)
                t.occupied = True
                t = m.get_tile(x, y, upper=True)
                t.occupied = True
            except IndexError:
                pass

    def set_party(self, x, y):
        self.set_occupied(x, y)
        for m in self.primary_meshes:
            try:
                t = m.get_tile(x, y)
                assert not t.bad_regardless
                t.party = True
                t = m.get_tile(x, y, upper=True)
                t.party = True
            except IndexError:
                pass

    def generate_heatmap(self, tiles):
        MAX_DISTANCE = 6
        heat_values = [100 ** (0.5 ** i) for i in range(MAX_DISTANCE+1)]
        heatmap = [[0] * self.width for _ in range(self.length)]
        heatmap[0][0] = None
        assert heatmap[1][0] is not None
        heatmap[0][0] = 0
        for (x, y) in tiles:
            for i in range(x-MAX_DISTANCE, x+MAX_DISTANCE+1):
                x_distance = abs(x-i)
                if not 0 <= i < self.width:
                    continue
                for j in range(y-MAX_DISTANCE, y+MAX_DISTANCE+1):
                    y_distance = abs(y-j)
                    if not 0 <= j < self.length:
                        continue
                    total_distance = x_distance + y_distance
                    if total_distance > MAX_DISTANCE:
                        continue
                    heatmap[j][i] += heat_values[total_distance]
        return heatmap

    def generate_occupied_heatmap(self, attribute='occupied'):
        occupied_tiles = self.get_tiles_compare_attribute(attribute, True)
        return self.generate_heatmap(occupied_tiles)

    def get_recommended_tiles(self, attribute='occupied'):
        avg_x = (self.width-1) / 2
        avg_y = (self.length-1) / 2
        heatmap = self.generate_occupied_heatmap(attribute)
        def sortfunc(x_y):
            x, y = x_y
            sig = '%s%s%s' % (x, y, self.signature)
            sig = md5(sig.encode('ascii')).hexdigest()
            uncenteredness = max(abs(x-avg_x), abs(y-avg_y)) / 100
            score = heatmap[y][x] - uncenteredness
            return score, sig

        candidates = self.get_tiles_compare_attribute('bad', False)
        ranked = sorted(candidates, key=sortfunc, reverse=True)
        return ranked

    def get_recommended_tiles_ally(self):
        ranked = self.get_recommended_tiles('party')
        return list(reversed(ranked))

    def get_recommended_tiles_enemy(self):
        partymap = self.generate_occupied_heatmap('party')
        enemymap = self.generate_occupied_heatmap('enemy')
        enemy_tiles = self.get_tiles_compare_attribute('enemy', True)
        def sortfunc(x_y):
            x, y = x_y
            if (x, y) in enemy_tiles:
                raise Exception('There should not be an enemy here.')
            sig = '%s%s%s' % (x, y, self.signature)
            sig = md5(sig.encode('ascii')).hexdigest()
            partyval = 1 + partymap[y][x]
            enemyval = 1 + enemymap[y][x]
            distances = []
            for ex, ey in enemy_tiles:
                distances.append(abs(x-ex) + abs(y-ey))
            distances = [1/(d**2) for d in distances]
            clumping = 1 + sum(distances)
            score = enemyval / (partyval * partyval * clumping)
            return score, sig

        candidates = self.get_tiles_compare_attribute('bad', False)
        ranked = sorted(candidates, key=sortfunc)
        return ranked

    @property
    def pretty_occupied_heatmap(self):
        heatmap = self.generate_occupied_heatmap()
        s = 'Y = %s\n' % (self.length-1)
        enemy_tiles = self.get_tiles_compare_attribute('enemy', True)
        party_tiles = self.get_tiles_compare_attribute('party', True)
        bad_tiles = self.get_tiles_compare_attribute('bad_regardless', True)
        for j in range(len(heatmap)-1, -1, -1):
            row = heatmap[j]
            for i, value in enumerate(row):
                if (i, j) in bad_tiles:
                    value = '--'
                elif (i, j) in party_tiles:
                    value = '##'
                elif (i, j) in enemy_tiles:
                    value = 'XX'
                else:
                    value = int(round(value))
                    value = '{0:0>2}'.format(value)
                s += value + ' '
            s = s.strip() + '\n'
        s += 'Y = 0'
        return s.strip()


class MeshObject(MapMixin):
    @classproperty
    def after_order(self):
        return [GNSObject]

    class Tile:
        def __init__(self, bytestring, x, y, upper=False):
            bytestring = [c for c in bytestring]
            self.terrain_type = bytestring[0] & 0x3F
            self.height = bytestring[2]
            self.depth = bytestring[3] >> 5
            self.slope_height = bytestring[3] & 0x1F
            self.slope_type = bytestring[4]
            self.impassable = (bytestring[6] >> 1) & 1
            self.uncursorable = bytestring[6] & 1
            self.occupied = False
            self.party = False
            self.unreachable = False
            self.x, self.y = x, y
            self.upper = upper

        @property
        def z(self):
            return self.height - self.depth

        @property
        def bad(self):
            if self.occupied or self.unreachable:
                return True
            if self.terrain_type in [0x12, 0x24]:
                # bad terrain : lava, water plant
                return True
            return self.bad_regardless

        @property
        def bad_regardless(self):
            if self.impassable | self.uncursorable:
                return True
            if self.slope_height > 2:
                return True
            if self.depth > 2:
                return True
            return False

        def set_unreachable(self, unreachable=True):
            self.unreachable = unreachable

        @property
        def enemy(self):
            return self.occupied and not self.party

    @property
    def gns(self):
        gnss = [gns for gns in GNSObject.every
                if gns.map_index == self.map_index]
        if len(gnss) == 1:
            return gnss[0]

    @property
    def terrain_addr(self):
        addr = int.from_bytes(self.data[0x68:0x68+4], byteorder='little')
        # TODO: addr >= 0xb4???
        return addr

    @property
    def width(self):
        return self.data[self.terrain_addr]

    @property
    def length(self):
        return self.data[self.terrain_addr+1]

    @cached_property
    def tiles(self):
        pointer = self.terrain_addr + 2
        block = self.data[pointer:pointer+2048]
        return [self.Tile(block[i*8:(i+1)*8], i % self.width, i // self.width)
                for i in range(self.width * self.length)]

    @cached_property
    def upper(self):
        pointer = self.terrain_addr + 2 + 2048
        block = self.data[pointer:pointer+2048]
        return [self.Tile(block[i*8:(i+1)*8], i % self.width, i // self.width,
                          upper=True)
                for i in range(self.width * self.length)]

    def get_tile(self, x, y, upper=False):
        index = (y * self.width) + x
        if upper:
            tile = self.upper[index]
        else:
            tile = self.tiles[index]
        assert (tile.x, tile.y) == (x, y)
        return tile

    def get_tiles_compare_attribute(self, *args, **kwargs):
        return self.gns.get_tiles_compare_attribute(*args, **kwargs)


class TextureObject(MapMixin): pass


class UnitObject(TableObject):
    DAYS_IN_MONTH = {1: 31, 2: 28, 3: 31, 4: 30, 5: 31, 6: 30,
                     7: 31, 8: 31, 9: 30, 10: 31, 11: 30, 12: 31}

    USED_MAPS = lange(0, 0x14b) + lange(0x180, 0x1d6)
    FIXED_WEATHER = [0x19f, 0x1b5, 0x1c2]

    @property
    def entd(self):
        return self.index >> 4

    @property
    def neighbors(self):
        if hasattr(self, '_neighbors'):
            return self._neighbors

        neighbors_dict = defaultdict(list)
        for u in UnitObject.every:
            neighbors_dict[u.entd].append(u)

        for u in UnitObject.every:
            u._neighbors = neighbors_dict[u.entd]

        return self.neighbors

    @property
    def character_name(self):
        name_index = self.old_data['name_index']
        name = names.characters[name_index]
        if not name.strip():
            return '{0:0>2X}-NO-NAME'.format(name_index)
        return name

    @property
    def is_ally(self):
        return not (
            self.get_bit('enemy_team') or self.get_bit('alternate_team'))

    @property
    def is_present(self):
        return (
            self.get_bit('randomly_present') or self.get_bit('always_present'))

    @property
    def is_unimportant(self):
        if not self.is_present:
            return True
        if self.character_name == 'RANDOM GENERIC':
            return True
        if 'NO-NAME' in self.character_name:
            return True
        return False

    @property
    def map(self):
        indexes = {e.map_index for e in EncounterObject.every
                   if e.entd == self.entd}
        if len(indexes) == 1:
            return GNSObject.get(list(indexes)[0])

    @property
    def old_map(self):
        indexes = {e.old_data['map_index'] for e in EncounterObject.every
                   if e.old_data['entd'] == self.entd}
        if len(indexes) == 1:
            return GNSObject.get(list(indexes)[0])

    def fix_facing(self):
        # 0: south, 1: west, 2: north, 3: east
        m = self.map
        dirdict = {
            "west": self.x, "south": self.y,
            "east": m.width - self.x, "north": m.length - self.y}
        facedict = {
            "west": 3, "south": 2, "east": 1, "north": 0}
        lowest = min(dirdict.values())
        candidates = sorted([v for (k, v) in facedict.items()
                             if dirdict[k] == lowest])
        chosen = random.choice(candidates)
        self.facing &= 0xFC
        self.facing |= chosen

    @property
    def is_upper(self):
        return bool(self.facing & 0x80)

    def set_upper(self, upper):
        if upper:
            self.facing |= 0x80
        else:
            self.facing &= 0x7f

    def relocate(self, x, y):
        if self.is_ally:
            self.map.set_party(x, y)
        else:
            self.map.set_occupied(x, y)
        self.x = x
        self.y = y
        self.set_upper(False)
        if not self.map.get_tile_attribute(self.x, self.y, 'bad_regardless',
                                           upper=True):
            if random.choice([True, True, False]):
                self.set_upper(True)

    def find_appropriate_position(self):
        if self.is_ally:
            tiles = self.map.get_recommended_tiles_ally()
        else:
            tiles = self.map.get_recommended_tiles_enemy()

        max_index = len(tiles)-1
        index = random.randint(random.randint(0, max_index), max_index)
        x, y = tiles[index]

        self.relocate(x, y)
        self.fix_facing()

    def relocate_nearest_good_tile(self):
        neighbor_coordinates = [(u.x, u.y) for u in self.neighbors
                                if u.is_present]
        valid_tiles = self.map.get_tiles_compare_attribute('bad', False)
        for distance in range(16):
            candidates = [(x, y) for (x, y) in valid_tiles
                          if abs(x-self.x) + abs(y-self.y) <= distance
                          and (x, y) not in neighbor_coordinates]
            if candidates:
                x, y = random.choice(candidates)
                self.relocate(x, y)
                break
        else:
            raise Exception('No good tiles.')

    def preprocess(self):
        if self.index == 0x153d and self.is_unimportant:
            self.set_bit('always_present', False)
            self.old_data['misc2'] = self.misc2

    def preclean(self):
        if self.is_present and self.map is not None:
            badness = self.map.get_tile_attribute(
                self.x, self.y, 'bad_regardless', upper=self.is_upper)
            try:
                assert badness is not True
                if badness is not False:
                    assert (self.x == self.old_data['x'] and
                            self.y == self.old_data['y'] and
                            self.map == self.old_map and False in badness)
            except AssertionError:
                self.relocate_nearest_good_tile()
                self.preclean()

    def cleanup(self):
        if self.get_bit('always_present'):
            for u in self.neighbors:
                if u.get_bit('always_present') and u is not self:
                    assert (u.x, u.y) != (self.x, self.y) or (
                        u.is_unimportant and self.is_unimportant)


class PropositionObject(TableObject):
    def cleanup(self):
        if 1 <= self.unlocked <= 5:
            self.unlocked = 1


class PropositionJPObject(TableObject): pass
class FormationPaletteObject(TableObject): pass
class SpritePaletteObject(TableObject): pass


if __name__ == '__main__':
    try:
        print('FINAL FANTASY TACTICS Rumble: Chaos: >>The Crashdown<< REMAKE'
              '\nRandomizer version %s.\n' % VERSION)

        ALL_OBJECTS = [g for g in globals().values()
                       if isinstance(g, type) and issubclass(g, TableObject)
                       and g not in [TableObject]]
        codes = {
            'novanilla': ['novanilla'],
            }
        run_interface(ALL_OBJECTS, snes=False, codes=codes,
                      custom_degree=True, custom_difficulty=True)

        clean_and_write(ALL_OBJECTS)

        write_cue_file()
        finish_interface()

    except Exception:
        print(format_exc())
        input('Press Enter to close this program. ')
