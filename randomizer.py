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

    randomselect_attributes = [
        ('hpgrowth', 'hpmult'),
        ('mpgrowth', 'mpmult'),
        ('spdgrowth', 'spdmult'),
        ('pagrowth', 'pamult'),
        ('magrowth', 'mamult'),
        'move', 'jump', 'evade',
        ]

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
            if 'NO-NAME' not in u.character_name:
                character_jobs[u.character_name].add(u.old_data['job'])

        JobObject._character_jobs = {}
        for name in character_jobs:
            JobObject._character_jobs[name] = [
                JobObject.get(j) for j in sorted(character_jobs[name])
                if JobObject.get(j).is_special]

        return JobObject.character_jobs

    @property
    def is_generic(self):
        return 0x4a <= self.index <= 0x5d

    @property
    def is_monster(self):
        return self.index >= 0x5e and self.index != 0x97

    @property
    def is_special(self):
        return 1 <= self.index <= 0x49 or self.index == 0x97

    @property
    def name(self):
        if self.is_generic:
            return self.GENERIC_NAMES[self.index-0x4a].upper()
        else:
            return 'JOB {0:0>2X}'.format(self.index)

    def magic_mutate_bits(self):
        super().magic_mutate_bits(random_degree=self.random_degree ** 0.5)


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

    @property
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
    def mesh(self):
        for m in MeshObject.every:
            if m.map_index == self.map_index:
                return m

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
        if self.mesh is None:
            return

        if self.map_index not in MoveFindObject.done_locations:
            MoveFindObject.done_locations[self.map_index] = set()

        if random.random() < self.random_degree ** 0.5:
            valid_locations = self.mesh.get_tiles_compare_attribute(
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


class FormationObject(TableObject): pass
class EncounterObject(TableObject): pass


class MapMixin(TableObject):
    @property
    def map_index(self):
        filename = path.split(self.filename)[-1]
        base, extension = filename.split('.')
        return int(base[-3:])

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


class MeshObject(MapMixin):
    @classproperty
    def after_order(self):
        return [GNSObject]

    class Tile:
        def __init__(self, bytestring, x, y):
            bytestring = [c for c in bytestring]
            self.terrain_type = bytestring[0] & 0x3F
            self.height = bytestring[2]
            self.depth = bytestring[3] >> 5
            self.slope_height = bytestring[3] & 0x1F
            self.slope_type = bytestring[4]
            self.impassable = (bytestring[6] >> 1) & 1
            self.uncursorable = bytestring[6] & 1
            self.occupied = 0
            self.party = 0
            self.upper = 0
            self.unreachable = 0
            self.x, self.y = x, y

        @property
        def bad(self):
            if self.occupied or self.unreachable:
                return 1
            if self.terrain_type in [0x12, 0x24]:
                # bad terrain : lava, water plant
                return 1
            return self.bad_regardless

        @property
        def bad_regardless(self):
            if self.impassable | self.uncursorable:
                return 1
            if self.slope_height > 2:
                return 1
            if self.depth > 2:
                return 1
            return 0

        def set_unreachable(self, unreachable=1):
            self.unreachable = unreachable

        def set_occupied(self, occupied=1):
            self.occupied = occupied

        def set_party(self, party=1):
            assert not self.occupied
            self.party = party
            self.set_occupied()

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
        return [self.Tile(block[i*8:(i+1)*8], i % self.width, i // self.width)
                for i in range(self.width * self.length)]

    @classmethod
    def get_by_map_index(self, map_index):
        return [m for m in MeshObject.every if m.map_index == map_index]

    def get_tile(self, x, y):
        index = (y * self.width) + x
        tile = self.tiles[index]
        assert (tile.x, tile.y) == (x, y)
        return tile

    def get_tiles_compare_attribute(self, attribute, value,
                                    compare_function=None):
        if compare_function is None:
            compare_function = lambda a, b: a == b
        meshes = MeshObject.get_by_map_index(self.map_index)
        meshes = [m for m in meshes if m.width * m.length > 0]
        width = min(m.width for m in meshes)
        length = min(m.length for m in meshes)
        coordinates = set()
        for y in range(length):
            for x in range(width):
                values = {getattr(m.get_tile(x, y), attribute) for m in meshes}
                if all(compare_function(v, value) for v in values):
                    coordinates.add((x, y))
        return sorted(coordinates)


class TextureObject(MapMixin): pass


class UnitObject(TableObject):
    DAYS_IN_MONTH = {1: 31, 2: 28, 3: 31, 4: 30, 5: 31, 6: 30,
                     7: 31, 8: 31, 9: 30, 10: 31, 11: 30, 12: 31}

    USED_MAPS = lange(0, 0x14b) + lange(0x180, 0x1d6)
    FIXED_WEATHER = [0x19f, 0x1b5, 0x1c2]

    @property
    def map_id(self):
        return self.index >> 4

    @property
    def character_name(self):
        name_index = self.old_data['name_index']
        name = names.characters[name_index]
        if not name.strip():
            return '{0:0>2X}-NO-NAME'.format(name_index)
        return name


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
