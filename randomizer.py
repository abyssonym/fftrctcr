from randomtools.tablereader import (
    TableObject, addresses, names, get_activated_patches, get_open_file,
    mutate_normal, get_seed, get_global_label, tblpath, remove_unused_file,
    get_random_degree, get_difficulty, write_patch,
    SANDBOX_PATH, get_psx_file_manager)
from randomtools.utils import (
    classproperty, cached_property, clached_property,
    read_lines_nocomment, utilrandom as random)
from randomtools.interface import (
    run_interface, clean_and_write, finish_interface,
    get_activated_codes, get_flags, get_outfile,
    write_cue_file)

import randomtools.xml_patch_parser as xml_patch_parser

from collections import Counter, defaultdict
from hashlib import md5
from math import ceil
from os import path, walk, environ, stat, listdir
from shutil import copyfile
from string import digits, ascii_lowercase, ascii_uppercase
from sys import argv
from traceback import format_exc

import re


VERSION = '4'
ALL_OBJECTS = None
DEBUG = environ.get('DEBUG')

XML_PATCH_CONFIG_FILEPATH = path.join('custom', 'xml_patches', 'patches.cfg')


def lange(*args):
    return list(range(*args))


def hashstring(s):
    return md5(s.encode('ascii')).hexdigest()


def rot90(array):
    return list(reversed(list(zip(*array))))


def hexify(data):
    return '-'.join(['{0:0>2X}'.format(c) for c in data])


class MutateBoostMixin(TableObject):
    def mutate(self):
        super().mutate()
        for attr in self.mutate_attributes:
            minval, maxval = self.mutate_attributes[attr]
            value = getattr(self, attr)
            if minval <= value <= maxval:
                while random.random() < (self.random_degree ** 2) / 2:
                    value += random.randint(-1, 1)
                    value = max(minval, min(maxval, value))
                    setattr(self, attr, value)


class AbilityObject(TableObject):
    flag = 's'
    custom_random_enable = flag

    mutate_attributes = {
        'jp_cost': None,
        'learn_chance': None,
        }

    INVITATION = 0x74
    CHARGE_20 = 0x19d
    BALL = 0x189
    JUMPS = lange(0x18a, 0x196)
    MP_SWITCH = 0x1bd
    TWO_SWORDS = 0x1dd
    SHORT_CHARGE = 0x1e2
    NON_CHARGE = 0x1e3
    TELEPORT2 = 0x1f3
    DUMMIED_ABILITIES = (NON_CHARGE, TELEPORT2)
    MP_RESTORE_INNATES = [0x1ee, 0x1b6, 0x1b0]
    MAINTENANCE = 0x1db

    @property
    def rank(self):
        if self.index in JobObject.BANNED_RSMS:
            return -1
        if self.index in SkillsetObject.BANNED_SKILLS:
            return -1
        self.preprocess()
        return self.old_data['jp_cost']

    @cached_property
    def ability_attributes(self):
        try:
            return AbilityAttributesObject.get(self.index)
        except KeyError:
            return None

    @property
    def ability_type(self):
        return self.misc_type & 0xF

    @property
    def is_reaction(self):
        return self.ability_type == 7

    @property
    def is_support(self):
        return self.ability_type == 8

    @property
    def is_movement(self):
        return self.ability_type == 9

    @property
    def is_action(self):
        return (1 <= self.index <= self.CHARGE_20
                and self.index not in self.JUMPS
                and self.ability_type not in (7, 8, 9))

    @property
    def requires_sword(self):
        if not self.ability_attributes:
            return False
        return (self.ability_attributes.get_bit('require_sword')
                or self.ability_attributes.get_bit('require_materia_blade'))

    @clached_property
    def action_pool(self):
        return [a for a in AbilityObject.ranked
                if a.is_action and a.rank >= 0 and a.ability_attributes]

    @clached_property
    def reaction_pool(self):
        return [a for a in AbilityObject.ranked
                if a.is_reaction and a.rank >= 0]

    @clached_property
    def support_pool(self):
        return [a for a in AbilityObject.ranked
                if a.is_support and a.rank >= 0]

    @clached_property
    def movement_pool(self):
        return [a for a in AbilityObject.ranked
                if a.is_movement and a.rank >= 0]

    @clached_property
    def passive_pool(self):
        return (self.reaction_pool + self.support_pool + self.movement_pool)

    def preprocess(self):
        if self.index in self.DUMMIED_ABILITIES:
            self.jp_cost = 0
            self.old_data['jp_cost'] = self.jp_cost

    @property
    def restores_mp(self):
        return self.index in self.MP_RESTORE_INNATES

    def cleanup(self):
        if self.jp_cost == 0 and not self.get_bit('no_learn_with_jp'):
            ratio = (random.random() +
                     random.random() + random.random()) / 3
            self.jp_cost = ratio * 9999
        self.jp_cost = int(round(self.jp_cost, -1))
        if self.jp_cost >= 10000:
            self.jp_cost = 9999


class AbilityAttributesObject(MutateBoostMixin):
    flag = 'a'
    flag_description = 'abilities'
    custom_random_enable = flag

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

        if self.get_bit('require_materia_blade'):
            self.set_bit('require_materia_blade', False)
            self.set_bit('require_sword', True)


class AbilityStatusObject(TableObject):
    flag = 'y'
    flag_description = 'ability and weapon status effects'
    custom_random_enable = flag

    def mutate(self):
        AbilityAttributesObject.get(self.index).mutate_status()


class JobStatsObject(TableObject):
    flag = 'j'
    flag_description = 'job stats'
    custom_random_enable = flag


class JobInnatesObject(TableObject):
    flag = 'i'
    flag_description = 'job innates'
    custom_random_enable = flag


class JobObject(TableObject):
    GENERIC_NAMES = [
        "squire", "chemist", "knight", "archer", "monk", "priest", "wizard",
        "timemage", "summoner", "thief", "mediator", "oracle", "geomancer",
        "lancer", "samurai", "ninja", "calculator", "bard", "dancer", "mime",
        ]
    SQUIRE_INDEX = 0x4a
    MIME_INDEX = 0x5d
    CHOCOBO_INDEX = 0x5e

    ARC_WITCH = 0x21
    ALTIMA_NICE_BODY = 0x41
    ALTIMA_PERFECT_BODY = 0x49

    VALID_INNATE_STATUSES = 0xc2fcc12a10
    VALID_START_STATUSES = (VALID_INNATE_STATUSES |
                            0x1c02300000)
    BENEFICIAL_STATUSES =   0xc278600000
    RERAISE_STATUS =        0x0000200000
    FAITH_STATUS =          0x8000000000
    INNOCENT_STATUS =       0x4000000000
    INVITE_STATUS =         0x0000004000
    FLOAT_STATUS =          0x0000400000
    DEAD_STATUS =           0x0000000020

    BANNED_RSMS = [0x1bb, 0x1e1, 0x1e4, 0x1e5, 0x1f1]
    LUCAVI_INNATES = (lange(0x1a6, 0x1a9) + [0x1aa] + lange(0x1ac, 0x1b0)
                      + lange(0x1b1, 0x1b4) + [0x1b5, 0x1ba, 0x1bd, 0x1be]
                      + lange(0x1c0, 0x1c6)
                      + lange(0x1d1, 0x1d6) + [0x1d8, 0x1dd, 0x1e3]
                      + [0x1e7, 0x1e8]
                      + lange(0x1eb, 0x1ee) + [0x1f2, 0x1f3, 0x1fa, 0x1fb]
                      ) + AbilityObject.MP_RESTORE_INNATES

    LUCAVI_ORDER = [0x43, 0x3c, 0x3e, 0x45, 0x40, 0x41, 0x97, 0x49]
    MONSTER_JOBS = lange(0x5e, 0x8e) + [0x90, 0x91, 0x96, 0x99, 0x9a]
    STORYLINE_RECRUITABLE_NAMES = {
        'Ramza', 'Mustadio', 'Agrias', 'Meliadoul', 'Rafa', 'Malak', 'Orlandu',
        'Beowulf', 'Cloud', 'Reis', 'Balthier', 'Ashley',
        }

    GROUP_RECRUITABLE = 1
    GROUP_LUCAVI = 2
    GROUP_MONSTER = 3
    GROUP_SPECIAL = 4

    LUCAVI_FACTOR = 1.3
    ENEMY_FACTOR = 1.0

    RANK_OVERRIDES = {0x7b: 99999}

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
    def STORYLINE_RECRUITABLE_NAMES(self):
        STORYLINE_RECRUITABLE_NAMES = {
            'Ramza', 'Mustadio', 'Agrias', 'Meliadoul', 'Rafa', 'Malak',
            'Orlandu', 'Beowulf', 'Cloud', 'Reis',
            }
        if get_global_label() == 'FFT_TLW':
            STORYLINE_RECRUITABLE_NAMES |= {'Balthier', 'Ashley'}
        return STORYLINE_RECRUITABLE_NAMES

    @classproperty
    def TLW_DARK_KNIGHTS(self):
        if get_global_label() == 'FFT_TLW':
            return {0x37, 0x38}
        return set()

    @classproperty
    def random_degree(self):
        return JobStatsObject.random_degree

    @classproperty
    def after_order(self):
        return [JobReqObject]

    @clached_property
    def character_jobs(self):
        from collections import OrderedDict

        character_jobs = defaultdict(set)
        for u in UnitObject.every:
            if u.entd_index > ENTDObject.LAST_NONTEST:
                continue
            if u.has_unique_name:
                character_jobs[u.character_name].add(u.old_data['job_index'])

        JobObject._character_jobs = OrderedDict()
        for name in character_jobs:
            JobObject._character_jobs[name] = [
                JobObject.get(j) for j in sorted(character_jobs[name])
                if JobObject.get(j).is_special and j != 0]

        return JobObject._character_jobs

    @property
    def profile(self):
        generics = [j for j in JobObject.every if j.is_generic]
        if JobObject.TLW_DARK_KNIGHTS:
            j = JobObject.get(min(JobObject.TLW_DARK_KNIGHTS))
            assert j not in generics
            generics.append(j)

        if self not in generics:
            raise NotImplementedError

        s = '/={0:=<19}=\\\n'.format(self.name.upper())
        s += ('| {0:3} | {1:5} | {2:5} |\n'.format('', 'BASE', 'GROW'))
        s += ('|-----+-------+-------|\n')
        stats = ['hp', 'mp', 'pa', 'ma', 'spd']
        for stat in stats:
            mult_attr = '{0}mult'.format(stat)
            grow_attr = '{0}growth'.format(stat)

            f = lambda j: getattr(j, mult_attr)
            g = lambda j: 255 - getattr(j, grow_attr)

            mult_index = sorted(
                generics, key=lambda j: (f(j), g(j))).index(self)
            mult_rank = int(round((4*mult_index / float(len(generics)-1)))) + 1
            assert 1 <= mult_rank <= 5
            grow_index = sorted(
                generics, key=lambda j: (g(j), f(j))).index(self)
            grow_rank = int(round((4*grow_index / float(len(generics)-1)))) + 1
            assert 1 <= grow_rank <= 5
            s += '| {0:>3} | {1:5} | {2:5} |\n'.format(
                stat.upper(), '*'*mult_rank, '*'*grow_rank)
        s += '\\=====================/\n'

        return s.strip()

    @cached_property
    def character_name(self):
        names = [n for n in self.character_jobs
                 if self in self.character_jobs[n]]
        if not names:
            return 'NONE'
        if len(names) == 2 and 'RANDOM GENERIC' in names:
            names.remove('RANDOM GENERIC')
        return ','.join(sorted(names))

    @property
    def has_unique_name(self):
        for word in ('GENERIC', 'NONE'):
            if word in self.character_name:
                return False
        return True

    @cached_property
    def relatives(self):
        if self.index in self.TLW_DARK_KNIGHTS:
            return [j for j in JobObject.every
                    if j.index in self.TLW_DARK_KNIGHTS]
        if self.character_name in ['NONE', 'RANDOM GENERIC']:
            return [self]
        relatives = [j for j in JobObject.every
                     if j.character_name == self.character_name]
        relatives = sorted(relatives, key=lambda r: r.signature)
        return relatives

    @cached_property
    def canonical_relative(self):
        if (self.character_name in ['NONE', 'RANDOM GENERIC']
                and self.index not in self.TLW_DARK_KNIGHTS):
            return self
        temp = [r for r in self.relatives if not r.is_zero_growth_job]
        if temp:
            return temp[0]
        return self.relatives[0]

    @cached_property
    def is_canonical(self):
        return self.canonical_relative is self

    @property
    def is_generic(self):
        return JobObject.SQUIRE_INDEX <= self.index <= JobObject.MIME_INDEX

    @property
    def is_dead(self):
        status = (self.old_data['start_status'] |
                  self.old_data['innate_status'])
        return status & JobObject.DEAD_STATUS

    @clached_property
    def ranked_generic_jobs_candidates(self):
        generic_jobs = [j for j in JobObject.every if j.is_generic
                        and j.index != self.SQUIRE_INDEX]
        generic_jobs = sorted(
            generic_jobs, key=lambda j: (j.get_jp_total(),
                                         j.signature))
        return generic_jobs

    @cached_property
    def is_monster(self):
        return (self.index >= 0x5e and self.index in self.MONSTER_JOBS
                and not self.is_lucavi)

    @property
    def is_lucavi(self):
        return self.index in self.LUCAVI_ORDER

    @property
    def is_altima(self):
        return self.index in {self.ALTIMA_NICE_BODY, self.ALTIMA_PERFECT_BODY}

    @property
    def is_special(self):
        return self.is_lucavi or not (self.is_generic or self.is_monster)

    @cached_property
    def is_recruitable(self):
        if self.index in self.TLW_DARK_KNIGHTS and self.is_canonical:
            return True
        return self.is_generic or (self.is_canonical and self.character_name in
                                   self.STORYLINE_RECRUITABLE_NAMES)
    @property
    def sprite_id(self):
        if self.monster_sprite > 0:
            job_sprite = self.monster_portrait
        else:
            job_sprite = self.index
        return job_sprite

    @cached_property
    def intershuffle_group(self):
        if not self.intershuffle_valid:
            return -1
        if self.is_recruitable:
            return self.GROUP_RECRUITABLE
        if self.is_lucavi:
            return self.GROUP_LUCAVI
        if self.is_monster:
            return self.GROUP_MONSTER
        if self.index >= 0x5e:
            return -1
        return self.GROUP_SPECIAL

    @cached_property
    def is_zero_growth_job(self):
        for attr in self.mutate_attributes:
            if attr.endswith('growth') and self.old_data[attr] == 0:
                return True
        return False

    @cached_property
    def intershuffle_valid(self):
        if self.rank < 0:
            return False
        return not self.is_zero_growth_job

    @cached_property
    def avg_entd_level(self):
        levels = [e.avg_level for e in ENTDObject.valid_entds
                  if self in e.old_jobs]
        levels = [l for l in levels if l is not None]
        if not levels:
            return -1
        lowest = min(levels)
        avg = sum(levels) / len(levels)
        return ((2*lowest) + avg) / 3

    @property
    def skillset(self):
        return SkillsetObject.get(self.skillset_index)

    @property
    def rsms(self):
        return self.skillset.rsms

    @cached_property
    def jobreq(self):
        if not self.is_generic:
            return None
        if self.index == self.SQUIRE_INDEX:
            return None
        return JobReqObject.get_by_name(self.name)

    def get_jp_total(self):
        if self.jobreq:
            return self.jobreq.get_jp_total()
        return 0

    @property
    def rank(self):
        if self.index in self.RANK_OVERRIDES:
            return self.RANK_OVERRIDES[self.index]

        if self.is_recruitable:
            return 1

        if hasattr(self, '_rank'):
            return self._rank

        for j in JobObject.every:
            j._rank = j.avg_entd_level

        seen_together = defaultdict(set)
        for e in ENTDObject.every:
            if not e.is_valid:
                continue
            for j in e.old_jobs:
                seen_together[j] |= set(e.old_jobs)

        for j in JobObject.every:
            if j._rank < 0:
                ranks = [j2._rank for j2 in seen_together[j] if j2._rank >= 0]
                if ranks:
                    j._rank = sum(ranks) / len(ranks)

        for group in [self.GROUP_RECRUITABLE, self.GROUP_LUCAVI,
                      self.GROUP_MONSTER, self.GROUP_SPECIAL]:
            ranked = [j for j in JobObject.every if j._rank >=0 and
                      j.intershuffle_group == group]
            ranked = sorted(ranked,
                            key=lambda j: (j._rank, j.signature))
            for i, j in enumerate(ranked):
                j._rank = i + 1

        return self.rank

    @clached_property
    def ranked_monsters(self):
        return [j for j in JobObject.ranked
                if j.intershuffle_group == JobObject.GROUP_MONSTER]

    @property
    def name(self):
        if self.index in self.TLW_DARK_KNIGHTS:
            return 'dark knight'
        if self.is_generic:
            return self.GENERIC_NAMES[
                self.index-JobObject.SQUIRE_INDEX]
        else:
            return 'JOB {0:0>2X}'.format(self.index)

    @classmethod
    def get_by_name(self, name):
        if not hasattr(JobObject, '_by_name_dict'):
            JobObject._by_name_dict = {}
        if name in JobObject._by_name_dict:
            return JobObject._by_name_dict[name]

        jobs = [j for j in JobObject.every
                if j.name.lower()[:3] == name.lower()[:3]]
        if len(jobs) == 1:
            job = jobs[0]
        else:
            job = None

        JobObject._by_name_dict[name] = job
        return JobObject.get_by_name(name)

    def can_equip(self, item):
        return self.equips & item.equip_flag

    def magic_mutate_bits(self):
        if JobInnatesObject.flag not in get_flags():
            return
        random_degree = JobInnatesObject.random_degree

        for attr in ['start_status', 'innate_status']:
            if random.random() > (random_degree ** 0.5) / 2:
                continue
            if (attr == 'innate_status' and self.is_generic
                    and random.random() > (random_degree ** 0.5) / 2):
                continue
            while True:
                mask = (1 << random.randint(0, 39))
                if mask & self.VALID_START_STATUSES:
                    break
            value = getattr(self, attr)
            value ^= mask
            setattr(self, attr, value)
        super().magic_mutate_bits(random_degree=random_degree ** (1/2))

    def preprocess(self):
        self.jump &= 0x7f

        for attr in self.old_data:
            if attr.endswith('growth') and self.old_data[attr] == 0:
                setattr(self, attr, 0xff)

        if (self.index == JobObject.ALTIMA_NICE_BODY
                and self.old_data['skillset_index'] == 0x59):
            self.old_data['skillset_index'] = 0x7b
            self.skillset_index = 0x7b

    def randomize_innates(self):
        random_degree = JobInnatesObject.random_degree

        if self.is_lucavi:
            all_supports = [i for i in AbilityObject.support_pool
                            if i.index in self.LUCAVI_INNATES
                            and i.index != AbilityObject.SHORT_CHARGE]
            all_reactions = [i for i in AbilityObject.reaction_pool
                             if i.index in self.LUCAVI_INNATES]
            all_movements = [i for i in AbilityObject.movement_pool
                             if i.index in self.LUCAVI_INNATES]
            num_reactions = 1 + random.randint(0, 1) + random.randint(0, 1)
            num_movements = 1
            num_supports = 7 - (num_reactions + num_movements)

            mp_switch = AbilityObject.get(AbilityObject.MP_SWITCH)
            while True:
                reactions = random.sample(all_reactions, num_reactions)
                if (any([r.restores_mp for r in reactions])
                        and mp_switch not in reactions):
                    continue
                break
            assert len(set(reactions)) == num_reactions

            non_charge = AbilityObject.get(AbilityObject.NON_CHARGE)
            short_charge = AbilityObject.get(AbilityObject.SHORT_CHARGE)
            supports = random.sample(all_supports, num_supports)
            assert len(set(supports)) == num_supports
            if not set(supports) & {non_charge, short_charge}:
                supports[-1] = short_charge
            supports = sorted(
                supports, key=lambda s: (s in (short_charge, non_charge),
                                         supports.index(s)))
            assert supports[-1] in (short_charge, non_charge)

            while True:
                movement = random.choice(all_movements)
                if mp_switch in reactions or not movement.restores_mp:
                    break

            self._fixed_unit_reaction = reactions.pop().index
            self._fixed_unit_support = supports.pop().index
            self._fixed_unit_movement = movement.index
            assert len(supports + reactions) == 4
            self.innates = [i.index for i in supports + reactions]

        elif self.is_monster:
            innates = [AbilityObject.get(i) for i in self.innates if i > 0]
            old_supports = [i for i in innates if i.is_support]
            old_reactions = [i for i in innates if i.is_reaction]
            old_movements = [i for i in innates if i.is_movement]
            assert len(old_reactions) == 1
            new_reaction = random.choice(AbilityObject.reaction_pool)
            new_other = old_supports + old_movements
            while len(new_other) < 3:
                chosen = random.choice(AbilityObject.support_pool +
                                       AbilityObject.movement_pool)
                if chosen not in new_other:
                    new_other.append(chosen)
            new_innates = sorted(new_other, key=lambda i: i.index)
            new_innates.insert(2, new_reaction)
            assert len(new_innates) == 4
            self.innates = [ni.index for ni in new_innates]

        elif not self.is_lucavi:
            for i, innate in enumerate(self.innates):
                if innate != 0 and random.random() > random_degree ** 2:
                    continue
                other = random.choice(
                    self.get_similar(wide=True).old_data['innates'])
                if other == 0:
                    continue

                if (other not in self.innates
                        and random.random() > random_degree):
                    if not AbilityObject.get(other).is_support:
                        continue
                    self.innates[i] = other
                else:
                    if random.random() > random_degree:
                        pool = AbilityObject.support_pool
                    else:
                        pool = AbilityObject.passive_pool
                    self.innates[i] = random.choice(pool).index

    def randomize_arc_witch(self):
        generics = JobObject.ranked_generic_jobs_candidates
        for attr in self.old_data:
            if attr == 'skillset_index':
                continue
            chosen = random.choice(generics)
            setattr(self, attr, chosen.old_data[attr])
        self.skillset_index = SkillsetObject.CHAOS

    def randomize(self):
        self.randomize_innates()
        if self.index == self.ARC_WITCH:
            self.randomize_arc_witch()

    def boost_stats(self, factor):
        for attrs in self.randomselect_attributes:
            if attrs in ['move', 'jump']:
                random_difficulty = self.random_difficulty ** 0.25
            else:
                random_difficulty = self.random_difficulty

            if not isinstance(attrs, tuple):
                attrs = (attrs,)
            for attr in attrs:
                value = getattr(self, attr)
                ratio = sum([random.random() for _ in range(3)]) / 3
                if attr.endswith('growth'):
                    boost = value / (random_difficulty ** factor)
                else:
                    boost = value * (random_difficulty ** factor)
                value = (value * ratio) + (boost * (1-ratio))
                value = max(0, min(0xff, value))
                setattr(self, attr, int(round(value)))

    def mutate(self):
        super().mutate()
        if self.is_lucavi:
            self.boost_stats(self.LUCAVI_FACTOR)
        elif not (self.is_generic or self.canonical_relative.is_recruitable):
            self.boost_stats(self.ENEMY_FACTOR)

    def preclean(self):
        for attr in ('move', 'jump'):
            value = getattr(self, attr)
            if value < 3:
                if random.random() > self.random_degree ** 2:
                    value = max(value, 3)
                else:
                    value = max(value, 2)
                setattr(self, attr, value)

        if self.old_data['jump'] & 0x80:
            self.jump |= 0x80

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

        if self.is_lucavi:
            random_degree = JobInnatesObject.random_degree
            self.immune_status &= (((2**40)-1) ^ self.BENEFICIAL_STATUSES)
            if random.choice([True, False]):
                self.immune_status |= self.FAITH_STATUS
            if random.choice([True, False]):
                self.immune_status |= self.INNOCENT_STATUS
            for i in range(40):
                if random.random() > random_degree:
                    self.immune_status |= (
                        self.old_data['immune_status'] & (1 << i))
            if (random.random() > random_degree ** 2
                    or random.choice([True, False])):
                self.innate_status &= self.BENEFICIAL_STATUSES
                self.start_status &= self.BENEFICIAL_STATUSES

        if self.is_generic and self.random_difficulty > 1:
            generics = ([JobObject.get(JobObject.SQUIRE_INDEX)]
                        + self.ranked_generic_jobs_candidates)
            max_index = len(generics) - 1
            index = generics.index(self)
            ratio = index / max_index
            assert 0 <= ratio <= 1

            multiplier = (self.random_difficulty ** 0.5)
            assert multiplier >= 1
            if ratio < 0.5:
                multiplier = 1 / multiplier
            elif ratio == 0.5:
                multiplier = 1
            extremity = abs(2 * (ratio - 0.5))
            assert 0 <= extremity <= 1
            multiplier = (extremity * multiplier) + ((1-extremity) * 1)
            assert multiplier > 0
            if ratio < 0.5:
                assert multiplier < 1
            elif ratio > 0.5:
                assert multiplier > 1
            else:
                assert multiplier == 1

            for attrs in self.randomselect_attributes:
                if isinstance(attrs, tuple):
                    for attr in attrs:
                        variance = sum(random.random() for _ in range(3)) / 3
                        mult = (multiplier * variance) + (1 - variance)
                        assert mult > 0
                        value = getattr(self, attr)
                        if attr.endswith('growth'):
                            value /= mult
                        if attr.endswith('mult'):
                            value *= mult
                        value = max(0, min(0xff, int(round(value))))
                        setattr(self, attr, value)

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
                oldvalue = self.old_data[attr]
                if 0 in (value, oldvalue):
                    value = max(value, oldvalue)
                    oldvalue = value
                difference = max(value, oldvalue) / min(value, oldvalue)
                assert difference >= 1
                if attr.endswith('growth'):
                    value = oldvalue / difference
                else:
                    value = oldvalue * difference
                value = max(0, min(0xff, int(round(value))))
                setattr(self, attr, value)

        if JobInnatesObject.flag not in get_flags():
            for attrs in self.magic_mutate_bit_attributes:
                if not isinstance(attrs, tuple):
                    attrs = (attrs,)
                for attr in attrs:
                    setattr(self, attr, self.old_data[attr])

        if self.index == self.SQUIRE_INDEX:
            for attrs in self.randomselect_attributes:
                if not isinstance(attrs, tuple):
                    attrs = (attrs,)
                for attr in attrs:
                    if attr.endswith('growth') or attr.endswith('mult'):
                        value = max(getattr(self, attr), self.old_data[attr])
                        setattr(self, attr, value)
                    else:
                        setattr(self, attr, self.old_data[attr])
            self.start_status &= self.BENEFICIAL_STATUSES
            self.innate_status &= self.BENEFICIAL_STATUSES

        if JobStatsObject.flag not in get_flags():
            for attrs in self.randomselect_attributes:
                if not isinstance(attrs, tuple):
                    attrs = (attrs,)
                for attr in attrs:
                    setattr(self, attr, self.old_data[attr])

        if ('easymodo' in get_activated_codes() and not
                (self.is_generic or self.canonical_relative.is_recruitable)):
            for attr in self.old_data:
                if attr.endswith('growth'):
                    setattr(self, attr, 0xff)
                elif attr.endswith('mult'):
                    setattr(self, attr, 0)


class ItemObject(MutateBoostMixin):
    flag = 'p'
    flag_description = 'shop item availability'
    custom_random_enable = flag

    mutate_attributes = {
        'price': (0, 65000),
        'time_available': (1, 16),
        'enemy_level': (1, 99),
        }

    BANNED_ITEMS = [0x49]
    PRICELESS_ITEMS = [0x6a, 0x8f]
    CHAOS_BLADE = 0x25
    RIBBON = 0xAB
    REFLECT_MAIL = 0xB8
    THROWN_ITEM_TYPES = (0x20, 0x21)
    SWORD_ITEM_TYPES = (0x03, 0x04)

    @cached_property
    def rank(self):
        if self.index == 0:
            return -1

        rank = self.old_data['price']
        if self.priceless:
            rank += 65000
            rank += (self.old_data['enemy_level'] * 100)
        return rank

    @property
    def intershuffle_valid(self):
        return self.rank >= 0

    @property
    def is_equipment(self):
        return self.misc1 & 0xf8

    @clached_property
    def ranked_hands_candidates(self):
        candidates = [c for c in ItemObject.ranked if c.intershuffle_valid
                      and c.is_equipment and
                      (c.get_bit('weapon') or c.get_bit('shield'))]
        return candidates

    @clached_property
    def ranked_nohands_candidates(self):
        candidates = [c for c in ItemObject.ranked if c.intershuffle_valid
                      and c.is_equipment and not
                      (c.get_bit('weapon') or c.get_bit('shield'))]
        return candidates

    @property
    def equip_flag(self):
        byte = self.item_type // 8
        bit = self.item_type % 8
        bit = 7 - bit
        return (1 << bit) << (byte * 8)

    @property
    def priceless(self):
        if self.old_data['price'] <= 10:
            return True
        elif self.index in self.PRICELESS_ITEMS:
            return True

    @property
    def is_sword(self):
        return self.item_type in self.SWORD_ITEM_TYPES

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

    def cleanup(self):
        self.price = int(round(self.price, -1))
        if self.price > 500:
            self.price = int(round(self.price, -2))

        if self.index == 0:
            self.price = 0

        if self.item_type in self.THROWN_ITEM_TYPES:
            self.enemy_level = max(self.enemy_level, 5)


class WeaponObject(MutateBoostMixin):
    flag = 'w'
    custom_random_enable = flag

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
        if self.old_data['range'] >= 3:
            self.range = max(self.range, 3)


class WeaponStatusObject(TableObject):
    flag = 'y'
    custom_random_enable = flag

    def mutate(self):
        WeaponObject.get(self.index).mutate_status()


class WeaponProcObject(TableObject):
    flag = 'x'
    flag_description = 'weapon spell procs'
    custom_random_enable = flag

    def mutate(self):
        WeaponObject.get(self.index).mutate_proc()


class ShieldObject(TableObject):
    flag = 'w'
    custom_random_enable = flag

    mutate_attributes = {
        'physical_evade': (0, 0x50),
        'magic_evade': (0, 0x50),
        }

class ArmorObject(TableObject):
    flag = 'w'
    custom_random_enable = flag

    mutate_attributes = {
        'hp_bonus': (0, 0xfd),
        'mp_bonus': (0, 0xfd),
        }

class AccessoryObject(TableObject):
    flag = 'w'
    custom_random_enable = flag

    mutate_attributes = {
        'physical_evade': (0, 0x3c),
        'magic_evade': (0, 0x3c),
        }

class ChemistItemObject(TableObject):
    flag = 'w'
    custom_random_enable = flag

    mutate_attributes = {
        'zval': (1, 0xfd),
        }


class InflictStatusObject(TableObject):
    flag = 'y'
    custom_random_enable = flag

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
    custom_random_enable = flag

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

    def mutate(self):
        super().mutate()
        ItemObject.get(self.index).mutate_item_attributes()


class SkillsetObject(TableObject):
    flag = 's'
    flag_description = 'job skillsets'
    custom_random_enable = flag

    MATH_SKILLSETS = {0xa, 0xb, 0xc, 0x10}
    MATH = 0x15
    CHAOS = 0x7c
    BANNED_ANYTHING = {0x18}  # mimic
    BANNED_SKILLSET_SHUFFLE = {0, 1, 2, 3, 6, 8, 0x11, 0x12, 0x13, 0x14, 0x15,
                               0x18, 0x34, 0x38, 0x39, 0x3b, 0x3e, 0x9c, 0xa1
                               } | BANNED_ANYTHING

    TLW_DARK_KNIGHT_CANON = 0x4d
    TLW_DARK_KNIGHT_OTHER = 0x4e

    @classproperty
    def BANNED_SKILLS(self):
        if get_global_label() == 'FFT_TLW':
            return set([0xdc])
        else:
            return set([0x28, 0x2d, 0xdb, 0xdc] + lange(0x165, 0x16f))

    @clached_property
    def character_skillsets(self):
        skillsets = {}
        for name in JobObject.character_jobs:
            jobs = JobObject.character_jobs[name]
            skillsets[name] = []
            for j in jobs:
                try:
                    ss = j.skillset
                    skillsets[name].append(ss)
                except KeyError:
                    pass
        return skillsets

    @property
    def is_generic(self):
        if (get_global_label() == 'FFT_TLW'
                and self.index == self.TLW_DARK_KNIGHT_CANON):
            return True
        return 5 <= self.index <= 0x18

    @cached_property
    def is_recruitable(self):
        for name in JobObject.STORYLINE_RECRUITABLE_NAMES:
            skillsets = SkillsetObject.character_skillsets[name]
            if self in skillsets:
                return True
        return False

    @cached_property
    def is_altima_secondary(self):
        seconds = [u.old_data['secondary']
                   for u in ENTDObject.get(ENTDObject.FINAL_BATTLE).units
                   if u.old_job.is_altima]
        return self.index in seconds

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
    def action_indexes(self):
        return self.get_actions()

    @property
    def actions(self):
        return [AbilityObject.get(i) for i in self.action_indexes if i > 0]

    @property
    def old_action_indexes(self):
        return self.get_actions(old=True)

    @cached_property
    def requires_sword(self):
        return any(a.requires_sword for a in self.actions)

    @property
    def is_lucavi_appropriate(self):
        if all(a.requires_sword for a in self.actions):
            return False
        if any(a.ability_attributes.get_bit('random_hits')
                for a in self.actions if a.ability_attributes):
            return False
        if any(a.index == AbilityObject.BALL for a in self.actions):
            return False
        return True

    def set_actions(self, actions, order_new=None):
        assert 0 not in actions
        if order_new is not None:
            actions = sorted(actions)
            old_actions = [a for a in actions if a in self.old_action_indexes]
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
    def rsm_indexes(self):
        rsms = []
        for i, rsm in enumerate(self.rsmbytes):
            if self.rsmbits & (1 << (0x7-i)):
                rsm |= 0x100
            rsms.append(rsm)
        return rsms

    @property
    def rsms(self):
        return [AbilityObject.get(rsm_index)
                for rsm_index in self.rsm_indexes if rsm_index > 0]

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

    def absorb_skills(self, other, old=True):
        actions = [i for i in self.action_indexes if i > 0]
        if old:
            other_actions = other.old_action_indexes
        else:
            other_actions = other.action_indexes
        for i in other_actions:
            if i > 0 and i not in actions:
                actions.append(i)

        if len(actions) > 16:
            temp = random.sample(actions, 16)
            actions = [i for i in actions if i in temp]
        self.set_actions(actions)

    @classmethod
    def intershuffle_skills(self):
        rsms = set()
        rsm_count = 0
        job_actions = {}
        for name in JobObject.STORYLINE_RECRUITABLE_NAMES:
            skillsets = SkillsetObject.character_skillsets[name]
            actions = set()
            rsm_counts = []
            for ss in skillsets:
                rsms |= set(ss.rsm_indexes)
                rsm_counts.append(len([rsm for rsm in ss.rsm_indexes if rsm]))
                actions |= set(ss.action_indexes)
            rsm_count += max(rsm_counts)
            actions -= {0}
            job_actions[name] = actions

        for ss in SkillsetObject.every:
            if ss.is_generic:
                rsms |= set(ss.rsm_indexes)
                rsm_count += len([rsm for rsm in ss.rsm_indexes if rsm])

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
                actions = SkillsetObject.get(key).action_indexes
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
                actions = SkillsetObject.get(base).action_indexes
            actions = [a for a in actions if a not in exchange_skills[base]]
            actions += exchange_skills[inherit]
            actions = [a for a in sorted(set(actions)) if a > 0]
            if len(actions) > 16:
                actions = random.sample(actions, 16)
            final_actions[base] = actions

        rsms = [rsm for rsm in sorted(rsms) if rsm > 0]
        temp = list(rsms)
        while len(temp) < rsm_count:
            temp.append(random.choice(rsms))
        rsms = temp
        for rsm in AbilityObject.DUMMIED_ABILITIES:
            if get_global_label() != 'FFT_TLW':
                assert rsm not in rsms
            if rsm not in rsms:
                rsms.append(rsm)
        random.shuffle(rsms)

        final_rsms = defaultdict(set)
        candidates = sorted([name for name in shuffle_skillsets
                             if isinstance(name, str)])
        candidates += [sso.index for sso in SkillsetObject.every
                       if sso.is_generic
                       and sso.index not in SkillsetObject.BANNED_ANYTHING]
        is_generic = lambda sso: isinstance(sso, int)
        you_get_one = False
        for rsm in rsms:
            while True:
                chosen = random.choice(candidates)
                if (rsm in AbilityObject.DUMMIED_ABILITIES
                        and is_generic(chosen) and you_get_one):
                    continue
                if len(final_rsms[chosen]) >= 6:
                    continue
                final_rsms[chosen].add(rsm)
                if (rsm in AbilityObject.DUMMIED_ABILITIES
                        and is_generic(chosen)):
                    seed = str(get_seed())
                    if not ('420' in seed and '69' in seed):
                        you_get_one = True
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
                actions = [a for a in actions if a in ss.old_action_indexes
                           or a not in job_actions[name]]
                ss.set_actions(actions, order_new)
                ss.set_rsms(final_rsms[name])
                if ss in done_skillsets:
                    assert done_skillsets[ss] == name
                else:
                    done_skillsets[ss] = name
                ss.preshuffled = True

        for ss in SkillsetObject.every:
            if ss.is_generic:
                if ss.index in final_actions:
                    order_new = random.choice([True, False])
                    ss.set_actions(final_actions[ss.index], order_new)
                ss.set_rsms(final_rsms[ss.index])
                ss.preshuffled = True

            assert self.get(0x19).skills_are_subset_of(self.get(0x1a))
            assert self.get(0x1a).skills_are_subset_of(self.get(0x1b))

    @classmethod
    def intershuffle_skillsets(self):
        def pick_best_skillset(skillsets):
            max_skills = max({len(ss.actions) for ss in skillsets})
            candidates = [ss for ss in skillsets
                          if len(ss.actions) == max_skills]
            if len(candidates) == 1:
                return candidates[0]
            candidates = sorted(candidates, key=lambda c: c.index)
            return random.choice(candidates)

        character_skillsets = dict(self.character_skillsets)
        names = sorted(JobObject.STORYLINE_RECRUITABLE_NAMES)
        if get_global_label() == 'FFT_TLW':
            names.append('DARK KNIGHT')
        shuffled_names = list(names)
        random.shuffle(shuffled_names)
        for sending, receiving in zip(names, shuffled_names):
            if sending == receiving:
                continue

            if sending == 'DARK KNIGHT':
                best = SkillsetObject.get(SkillsetObject.TLW_DARK_KNIGHT_CANON)
            else:
                skillsets = character_skillsets[sending]
                best = pick_best_skillset(skillsets)

            if receiving == 'DARK KNIGHT':
                jobs = [j for j in JobObject.every
                        if j.old_data['skillset_index'] in
                        (SkillsetObject.TLW_DARK_KNIGHT_CANON,
                         SkillsetObject.TLW_DARK_KNIGHT_OTHER)]
            else:
                jobs = JobObject.character_jobs[receiving]

            for j in jobs:
                j.skillset_index = best.index

    @classmethod
    def intershuffle(self):
        self.intershuffle_skills()
        self.intershuffle_skillsets()

    def randomize(self):
        if self.is_altima_secondary and self.random_difficulty >= 1:
            actions = random.sample(AbilityObject.action_pool, 16)
            self.set_actions([a.index for a in actions])
            return

        if hasattr(self, 'preshuffled') and self.preshuffled:
            exponent = 3.5
        else:
            exponent = 2

        rsm_indexes = list(self.rsm_indexes)
        if len(rsm_indexes) < 6:
            rsm_indexes += ([0] * (6 - len(rsm_indexes)))
        assert len(rsm_indexes) == 6

        for i in range(len(rsm_indexes)):
            if random.random() < self.random_degree ** exponent:
                chosen = random.choice(AbilityObject.passive_pool).index
                if chosen not in rsm_indexes:
                    rsm_indexes[i] = chosen

        self.set_rsms([i for i in rsm_indexes if i > 0])

        action_indexes = list(self.action_indexes)
        if self.index in self.BANNED_SKILLSET_SHUFFLE:
            action_indexes = [i for i in action_indexes if i > 0 and not
                              (random.random() < self.random_degree
                                  and random.choice([True, False]))]
            self.set_actions(action_indexes, order_new=None)
            return

        if len(action_indexes) < 16:
            action_indexes += ([0] * (16 - len(action_indexes)))
        assert len(action_indexes) == 16

        for i in range(len(action_indexes)):
            if random.random() < self.random_degree ** exponent:
                chosen = random.choice(AbilityObject.action_pool).index
                if chosen not in action_indexes:
                    action_indexes[i] = chosen

        self.set_actions([i for i in action_indexes if i > 0], order_new=None)

        if self.index in self.MATH_SKILLSETS:
            for a in self.actions:
                if random.random() < ((self.random_degree ** 0.65) / 2):
                    a.ability_attributes.set_bit('math_skill', True)

    def skills_are_subset_of(self, other):
        return (set(self.actions) <= set(other.actions) and
                set(self.rsms) <= set(other.rsms))

    def preclean(self):
        if not (self.is_generic or self.is_recruitable):
            return
        for ability in self.actions + self.rsms:
            if (ability.get_bit('no_learn_with_jp') and
                    not ability.get_bit('learn_on_hit')):
                if ability in self.rsms or random.choice([True, False]):
                    ability.set_bit('no_learn_with_jp', False)
                elif ability in self.actions:
                    ability.set_bit('learn_on_hit', True)

    def cleanup(self):
        if (get_global_label() == 'FFT_TLW'
                and self.index == self.TLW_DARK_KNIGHT_OTHER):
            canon = self.get(self.TLW_DARK_KNIGHT_CANON)
            for attr in self.old_data:
                setattr(self, attr, getattr(canon, attr))
        while len(self.actionbytes) < len(self.old_data['actionbytes']):
            self.actionbytes.append(0)
        while len(self.rsmbytes) < len(self.old_data['rsmbytes']):
            self.rsmbytes.append(0)
        if self.action_indexes:
            assert all(action <= 0x1a5 for action in self.action_indexes)
            assert not (set(self.action_indexes) &
                        SkillsetObject.BANNED_SKILLS)
        if self.rsm_indexes:
            assert all(rsm >= 0x1a6 for rsm in self.rsm_indexes if rsm > 0)
            assert not (set(self.rsm_indexes) & SkillsetObject.BANNED_SKILLS)


class MonsterSkillsObject(TableObject):
    flag = 's'
    custom_random_enable = 'o'

    CHOCOBO_SKILLSET_INDEX = 0xb0

    @property
    def skillset_index(self):
        return self.index + self.CHOCOBO_SKILLSET_INDEX

    @property
    def skill_indexes(self):
        indexes = []
        for i, attack in enumerate(self.attackbytes):
            highbit = (self.highbits >> (7-i)) & 1
            if highbit:
                attack |= 0x100
            indexes.append(attack)
        return indexes

    @cached_property
    def old_skill_indexes(self):
        indexes = []
        for i, attack in enumerate(self.old_data['attackbytes']):
            highbit = (self.old_data['highbits'] >> (7-i)) & 1
            if highbit:
                attack |= 0x100
            indexes.append(attack)
        return indexes

    @property
    def skills(self):
        return [AbilityObject.get(i) for i in self.skill_indexes if i > 0]

    def set_skill_indexes(self, indexes):
        temp = []
        for i in indexes:
            if i not in temp:
                temp.append(i)
        indexes = temp
        self.attackbytes = [i & 0xff for i in indexes]
        self.highbits = 0
        done_skills = set()
        for (i, skill) in enumerate(indexes):
            if skill & 0x100:
                self.highbits |= (1 << (7-i))
        assert self.skill_indexes == indexes

    @cached_property
    def monster_type(self):
        monsters = [j for j in JobObject.every
                    if j.old_data['skillset_index'] == self.skillset_index]
        if len(monsters) == 1:
            monster_type = monsters[0].old_data['monster_portrait']
            assert monster_type > 0
            return monster_type

    @cached_property
    def family(self):
        return [m for m in MonsterSkillsObject.every
                if m.monster_type == self.monster_type]

    @clached_property
    def monster_skill_pool(self):
        return sorted({i for m in MonsterSkillsObject.every
                       for i in m.old_skill_indexes})

    def randomize(self):
        family_skill_pool = sorted({i for m in self.family
                                    for i in m.old_skill_indexes
                                    if i > 0})
        new_skills = []
        while len(new_skills) < 4:
            if random.random() < self.random_degree:
                if random.random() < self.random_degree:
                    pool = AbilityObject.action_pool
                else:
                    pool = self.monster_skill_pool
            else:
                pool = family_skill_pool
            chosen = random.choice(pool)
            if isinstance(chosen, AbilityObject):
                chosen = chosen.index
            if chosen in new_skills:
                continue
            if chosen > 0:
                new_skills.append(chosen)
        new_skills[:3] = sorted(new_skills[:3])
        self.set_skill_indexes(new_skills)


class PoachObject(TableObject):
    flag = 't'
    flag_description = 'trophies, poaches, move-find items'
    custom_random_enable = flag

    @property
    def monster_name(self):
        return names.monsters[self.index]

    @property
    def item_names(self):
        return names.items[self.common], names.items[self.rare]

    def mutate(self):
        self.common = ItemObject.get(self.common).get_similar(
            wide=True, random_degree=self.random_degree).index
        self.rare = ItemObject.get(self.rare).get_similar(
            wide=True, random_degree=self.random_degree).index

    def randomize(self):
        if random.random() < self.random_degree / 2:
            self.common, self.rare = self.rare, self.common

    def __repr__(self):
        return '{0:14} {1:15} {2:15}'.format(
            self.monster_name, *self.item_names)


class JobReqObject(TableObject):
    flag = 'r'
    flag_description = 'job requirements'
    custom_random_enable = flag

    BANNED_REQS = ('bar', 'dan')
    CALC_REQS = ('pri', 'wiz', 'tim', 'ora')

    @classproperty
    def jobtree(self):
        jobreqs = sorted(self.every, key=lambda j: (j.total_levels,
                                                    j.signature))
        jobtree = {}
        for j in jobreqs:
            jobtree[j] = set([])

        categorized = set([])
        for j in jobreqs:
            chosen = None
            for j2 in jobreqs:
                if j2.reqs_are_strict_subset_of(j) and j.get_req(j2.name) > 0:
                    if not chosen or chosen.reqs_are_strict_subset_of(j2):
                        chosen = j2
                    elif j2.reqs_are_strict_subset_of(chosen):
                        pass
                    else:
                        chosen = max(
                            [j2, chosen],
                            key=lambda j3: (
                                j3.total_levels + j.get_req(j3.name),
                                j.get_req(j3.name), j3.index))

            if chosen is not None:
                jobtree[chosen].add(j)
                categorized.add(j)

        def recurse(j):
            s = "%s:" % j.name.upper()
            prereqs = j.get_simplified_reqs()
            for key in sorted(JobObject.GENERIC_NAMES):
                key = key[:3]
                if key not in prereqs:
                    continue
                value = prereqs[key]
                if value > 0:
                    s += " %s %s," % (value, key[:3])
            s = s.strip(",")
            s += "\n"
            for j2 in sorted(jobtree[j], key=lambda j3: j3.name):
                s += recurse(j2) + "\n"
            s = s.strip()
            s = s.replace("\n", "\n    ")
            return s

        treestr = ""
        for j in sorted(jobtree.keys(), key=lambda j3: j3.name):
            if j not in categorized:
                treestr += recurse(j) + "\n\n"
        treestr = treestr.strip()

        if hasattr(self, 'DKM'):
            treestr = '{0}\n\nDKM: 1 {1}, 1 {2}\nDKF: 1 {3}, 1 {4}'.format(
                treestr,
                self.DKM[0].name, self.DKM[1].name,
                self.DKF[0].name, self.DKF[1].name)

        return treestr

    @classmethod
    def get_by_name(self, name):
        if not hasattr(JobReqObject, '_by_name_dict'):
            JobReqObject._by_name_dict = {}
        if name in JobReqObject._by_name_dict:
            return JobReqObject._by_name_dict[name]

        jros = [j for j in JobReqObject.every
                if j.name.lower() == name.lower()[:3]]
        if len(jros) == 1:
            jro = jros[0]
        else:
            jro = None

        JobReqObject._by_name_dict[name] = jro
        return JobReqObject.get_by_name(name)

    @property
    def job_index(self):
        return self.index + JobObject.SQUIRE_INDEX + 1

    @classmethod
    def get_by_job_index(self, job_index):
        jros = [j for j in JobReqObject.every if j.job_index == job_index]
        if len(jros) == 1:
            return jros[0]

    @property
    def name(self):
        return JobObject.GENERIC_NAMES[self.index+1][:3]

    @property
    def rank(self):
        return self.get_jp_total(old=True)

    @property
    def total_levels(self):
        return sum(self.get_recursive_reqs().values())

    @property
    def squire_only(self):
        for name in JobObject.GENERIC_NAMES:
            if name.lower().startswith('squ'):
                continue
            if self.get_req(name):
                return False
        return True

    @property
    def calculator_potential(self):
        if self.name == 'cal':
            cal_potential = JobJPReqObject.get(7).jp
        else:
            cal_req = self.get_req('cal')
            if cal_req > 0:
                cal_potential = JobJPReqObject.get(cal_req-1).jp
            else:
                return 0

        if self.name in self.CALC_REQS:
            mage_potential = JobJPReqObject.get(7).jp
        else:
            mage_potential = 0

        for name in self.get_recursive_reqs():
            req = self.get_req(name)
            if name in self.CALC_REQS and name != self.name and req > 0:
                mage_potential += JobJPReqObject.get(req-1).jp

        return cal_potential * mage_potential

    def get_jp_total(self, old=False):
        if old and hasattr(self, '_old_jp'):
            return self._old_jp
        levels = self.get_recursive_reqs(old=old).values()
        jps = [JobJPReqObject.get(level-1).jp for level in levels if level > 0]
        jp_total = sum(jps)
        if old:
            self._old_jp = jp_total
            return self.get_jp_total(old=old)
        return jp_total

    def get_recursive_reqs(self, old=False):
        names = [name[:3] for name in JobObject.GENERIC_NAMES]
        if hasattr(self, '_lockdown') and not old:
            if self._lockdown is None:
                self._lockdown = {name: self.get_req(name) for name in names}
            return dict(self._lockdown)

        reqs = defaultdict(int)
        done_names = set()
        while True:
            prev_reqs = dict(reqs)
            for name in names:
                if name in done_names:
                    continue
                level = self.get_req(name, old=old)
                if level > 0 or reqs[name] > 0:
                    reqs[name] = max(reqs[name], level)
                    other = JobReqObject.get_by_name(name)
                    if other is not None:
                        for other_name in names:
                            other_level = other.get_req(other_name, old=old)
                            reqs[other_name] = max(reqs[other_name],
                                                   other_level)
                    done_names.add(name)
            if reqs == prev_reqs:
                break

        return prev_reqs

    def reqs_are_subset_of(self, other):
        self_reqs, other_reqs = (self.get_recursive_reqs(),
                                 other.get_recursive_reqs())
        for job_prefix in JobObject.GENERIC_NAMES:
            job_prefix = job_prefix[:3]
            if (self_reqs[job_prefix]
                    > other_reqs[job_prefix]):
                return False
        return True

    def same_reqs(self, other):
        self_reqs, other_reqs = (self.get_recursive_reqs(),
                                 other.get_recursive_reqs())
        for job_prefix in JobObject.GENERIC_NAMES:
            job_prefix = job_prefix[:3]
            if (self_reqs[job_prefix]
                    != other_reqs[job_prefix]):
                return False
        return True

    def reqs_are_strict_subset_of(self, other):
        return self.reqs_are_subset_of(other) and not self.same_reqs(other)

    def get_simplified_reqs(self, old=False):
        reqs = self.get_recursive_reqs(old=old)
        for name in sorted(reqs):
            if name == 'squ':
                continue
            if reqs[name] <= 0:
                continue
            old_value = reqs[name]
            jro = JobReqObject.get_by_name(name)
            sub_reqs = jro.get_recursive_reqs(old=old)
            for sub_name in sub_reqs:
                if sub_reqs[sub_name] >= reqs[sub_name]:
                    reqs[sub_name] = 0
            assert reqs[name] == old_value
        reqs = {k: v for k, v in reqs.items() if v > 0}
        return reqs

    def get_req(self, job_prefix, old=False):
        job_prefix = job_prefix[:3].lower()
        for attr in self.old_data:
            if old:
                value = self.old_data[attr]
            else:
                value = getattr(self, attr)
            if attr.startswith(job_prefix):
                return value >> 4
            elif attr.endswith(job_prefix):
                return value & 0xf

    def set_req(self, job_prefix, level):
        if hasattr(self, '_lockdown'):
            raise Exception('Lockdown violation.')

        job_prefix = job_prefix[:3].lower()
        for attr in self.old_data:
            value = getattr(self, attr)
            if attr.startswith(job_prefix):
                value &= 0x0f
                value |= (level << 4)
                setattr(self, attr, value)
                break
            elif attr.endswith(job_prefix):
                value &= 0xf0
                value |= level
                setattr(self, attr, value)
                break

    def increment_req(self, job_prefix):
        value = self.get_req(job_prefix)
        if value < 8:
            self.set_req(job_prefix, value + 1)

    def clear_reqs(self):
        if hasattr(self, '_lockdown'):
            raise Exception('Lockdown violation.')

        for attr in self.old_data:
            setattr(self, attr, 0)

    def fill_reqs(self):
        for req, level in self.get_recursive_reqs().items():
            self.set_req(req, level)
        self._lockdown = None

    @clached_property
    def jp_increase_ratio(self):
        old_values = [jro.get_jp_total(old=True) for jro in self.every]
        new_values = [jro.get_jp_total() for jro in self.every]
        ratios = []
        for old, new in zip(sorted(old_values), sorted(new_values)):
            if min(old, new) == 0:
                continue
            ratio = new / old
            ratios.append(ratio)
        return (sum(ratios) / len(ratios))

    @classmethod
    def randomize_all(self):
        old_ranked = self.ranked
        jp_values = [jro.get_similar().get_jp_total(old=True)
                     for jro in old_ranked]
        max_jp = max(jp_values)
        jp_values = [mutate_normal(jp, 0, max_jp,
                                   random_degree=self.random_degree)
                     for jp in jp_values]
        boosted_values = []
        max_index = len(jp_values) - 1
        minval, maxval = min(jp_values), max(jp_values)
        for i, jp_value in enumerate(jp_values):
            ratio = (i / max_index) ** 2
            boosted_value = jp_value * (self.random_difficulty ** 2)
            randomness = sum(random.random() for _ in range(3)) / 3
            boosted_value = ((boosted_value * randomness) +
                             (jp_value * (1-randomness)))
            boosted_value = max(minval, min(boosted_value, maxval))
            boosted_values.append(boosted_value)
        jp_values = sorted(boosted_values)
        jp_values = [round(jp * 2, -2) // 2 for jp in jp_values]
        jp_values = sorted(jp_values)

        while True:
            job_pools = [[], []]
            if random.choice([True, False]):
                job_pools.append([])
            for name in JobObject.GENERIC_NAMES:
                random.choice(job_pools).append(name[:3])
            if all(job_pools):
                break

        prereqqed = {'squ': 0}
        salt = self.get(0).signature
        while True:
            if not jp_values:
                break

            candidates = ([name[:3] for name in JobObject.GENERIC_NAMES
                           if name[:3] not in prereqqed])
            if len(prereqqed) == 1:
                squ_pool = [p for p in job_pools if 'squ' in p][0]
                candidates = [c for c in candidates if c not in squ_pool]
            next_name = random.choice(candidates)
            jro = self.get_by_name(next_name)
            jro.clear_reqs()
            jp_value = jp_values[0]
            my_pool = [p for p in job_pools if next_name in p][0]
            reqqed = dict(prereqqed)
            for _ in range(1000):
                candidates = sorted(
                    reqqed, key=lambda k: (reqqed[k],
                                           hashstring('%s%s' % (k, salt))))
                candidates = [c for c in candidates
                              if c not in self.BANNED_REQS]
                if random.random() > max(self.random_degree ** 2, 0.01):
                    temp = [c for c in candidates if c in my_pool]
                    if temp:
                        candidates = temp

                max_index = len(candidates)-1
                index = int(round(
                    (random.random() ** (self.random_degree ** 0.25))
                    * max_index))
                index = max_index - index
                chosen = candidates[index]
                jro.increment_req(chosen)
                reqqed[chosen] += 1
                simpreqs = jro.get_simplified_reqs()
                for key, value in sorted(simpreqs.items()):
                    if key != 'squ' and value == 1:
                        jro.increment_req(key)
                if jro.get_jp_total() >= jp_value:
                    break
            else:
                continue

            if jro.name == 'cal':
                reqs = jro.get_recursive_reqs()
                if not any([reqs[job_prefix] > 0
                            for job_prefix in self.CALC_REQS]):
                    continue

            prereqqed = reqqed
            assert next_name not in prereqqed
            prereqqed[next_name] = 0
            jp_values = jp_values[1:]

        for jro in JobReqObject.every:
            jro.fill_reqs()

        if get_global_label() == 'FFT_TLW':
            JobReqObject.randomize_dark_knight()
        super().randomize_all()

    @classmethod
    def randomize_dark_knight(self):
        FILENAME = JobReqObject.get(0).filename
        f = get_open_file(FILENAME)
        MALE_ADDRESS = 0x17900
        FEMALE_ADDRESS = 0x17910

        addresses = {'DKM':   0x17900,
                     'DKF': 0x17910}
        for label in ('DKM', 'DKF'):
            for _ in range(1000):
                if label == 'DKM':
                    candidates = [jro for jro in JobReqObject.every
                                  if jro.name != 'dan']
                if label == 'DKF':
                    candidates = [jro for jro in JobReqObject.every
                                  if jro.name != 'bar']
                first = random.choice(candidates)
                others = [jro for jro in candidates if
                          not (jro.reqs_are_subset_of(first) or
                               first.reqs_are_subset_of(jro))]
                if label == 'DKF' and first in JobReqObject.DKM:
                    others = [o for o in others if o not in JobReqObject.DKM]
                if not others:
                    continue
                second = random.choice(others)
                first, second = tuple(sorted((first, second)))
                setattr(JobReqObject, label, (first, second))
                req_values = ['0'] * 20
                for jro in (first, second):
                    reqs = jro.get_recursive_reqs()
                    for prefix in reqs:
                        subreq = JobReqObject.get_by_name(prefix)
                        index = subreq.index+1 if subreq is not None else 0
                        newvalue = str(reqs[prefix])
                        if newvalue > req_values[index]:
                            req_values[index] = newvalue
                    assert req_values[jro.index + 1] == '0'
                    req_values[jro.index + 1] = '1'
                req_values = int(''.join(req_values), 0x10)
                f.seek(addresses[label])
                f.write(req_values.to_bytes(10, byteorder='big'))
                break
            else:
                setattr(JobReqObject, label, (None, None))
                f.seek(addresses[label])
                f.write(b'\x00' * 10)
            assert JobReqObject.DKM

    def cleanup(self):
        assert self.get_recursive_reqs()[self.name] == 0
        for name in JobObject.GENERIC_NAMES:
            assert 0 <= self.get_req(name[:3]) <= 8
        if self.name == 'cal':
            reqs = self.get_recursive_reqs()
            assert any([reqs[job_prefix] > 0
                        for job_prefix in self.CALC_REQS])
        for job_prefix in self.BANNED_REQS:
            assert job_prefix not in self.get_simplified_reqs()


class JobJPReqObject(TableObject):
    flag = 'r'
    custom_random_enable = flag

    ADVANCED_JP = [100, 200, 400, 700, 1100, 1600, 2200, 3000]

    def preprocess(self):
        if self.flag in get_flags():
            self.jp = self.jp * self.random_difficulty
        self.jp = int(round(self.jp * 2, -2) // 2)

    def cleanup(self):
        self.jp = min(self.jp, self.ADVANCED_JP[self.index])


class MoveFindObject(TableObject):
    flag = 't'
    custom_random_enable = flag

    done_locations = {}
    valid_locations = {}

    @classproperty
    def after_order(self):
        return [MeshObject, EncounterObject, ENTDObject]

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

    def randomize(self):
        if self.map is None:
            return

        if self.map_index not in MoveFindObject.done_locations:
            MoveFindObject.done_locations[self.map_index] = set()

        if ((self.x, self.y) == (0, 0)
                or random.random() < self.random_degree ** 0.5):
            if self.map_index in MoveFindObject.valid_locations:
                valid = MoveFindObject.valid_locations[self.map_index]
            else:
                valid = self.map.get_tiles_compare_attribute(
                    'bad', False)
                MoveFindObject.valid_locations[self.map_index] = valid

            valid_locations = [l for l in valid if l not in
                               MoveFindObject.done_locations[self.map_index]]
            new_location = random.choice(valid_locations)
            self.set_coordinates(*new_location)
            MoveFindObject.done_locations[self.map_index].add(new_location)

        template = random.choice([mfo for mfo in MoveFindObject.every
                                  if mfo.is_active])
        self.misc1 = template.old_data['misc1']
        if (not template.old_item_null and (
                self.old_item_null
                or random.random() < self.random_degree)):
            common, rare = (template.old_data['common'],
                            template.old_data['rare'])
        else:
            common, rare = self.common, self.rare
        self.common = ItemObject.get(common).get_similar(
            random_degree=self.random_degree, wide=True).index
        self.rare = ItemObject.get(rare).get_similar(
            random_degree=self.random_degree, wide=True).index


class FormationObject(TableObject):
    flag = 'f'
    custom_random_enable = flag

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

    @cached_property
    def encounters(self):
        return [e for e in EncounterObject.every if self in e.formations]

    @property
    def entd_index(self):
        entds = {e.entd_index for e in EncounterObject.every
                 if self in e.formations}
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
        recommended_tiles = self.map.get_recommended_tiles()
        compare_function = lambda a, b: a >= b
        depth_tiles = self.map.get_tiles_compare_attribute(
            'depth', 1, compare_function=compare_function)
        surface_tiles = [t for t in recommended_tiles if t not in depth_tiles]
        while True:
            if random.random() > self.random_degree ** 1.5:
                tiles = surface_tiles
            else:
                tiles = recommended_tiles
            max_index = len(tiles)-1
            factor = 1 - (random.random() ** (1 / (self.random_degree ** 0.7)))
            assert 0 <= factor <= 1
            index = int(round(max_index * factor))
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
            if not window:
                continue
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
            free_tiles = len(tiles) - len(window)
            if free_tiles + num_characters <= 16:
                continue
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
                and self.entd_index == ENTDObject.MUROND_HOLY_PLACE):
            assert all(e.map_index == 0x32 for e in self.encounters)
            self.map_index = 0x32
            self.old_data['map_index'] = 0x32


class EncounterObject(TableObject):
    flag = 'f'
    flag_description = 'enemy and ally formations'
    custom_random_enable = flag

    FIXED_SONGS = {0, 17, 18, 19, 20, 21, 22, 23, 24,
                   27, 28, 29, 30, 31, 32, 33, 35, 40,
                   41, 42, 43, 44, 45, 46, 47, 48, 49, 50,
                   51, 52, 53, 54, 55, 56, 57, 59, 60, 63, 64, 65,
                   69, 70, 71, 72, 73, 74, 75, 79, 98}
    DUMMIED_SONGS = set(range(81, 97)) - FIXED_SONGS
    CANDIDATE_SONGS = set(range(100)) - FIXED_SONGS
    used_music = set()
    ENDING_MUSIC = 0x45

    REPLACING_MAPS = [
        1, 4, 8, 9, 11, 14, 15, 18, 20, 21, 23, 24, 26, 37, 38,
        43, 46, 48, 51, 53, 62, 65, 68, 71, 72, 73, 75,
        76, 92, 93, 95, 96, 97, 98, 99, 100, 101, 102, 104,
        115, 116, 117, 118, 119, 125]
    DONE_MAPS = set()
    REPLACED_MAPS = set()

    @classmethod
    def set_class_constants(self):
        if get_global_label() == 'FFT_TLW':
            self.NO_REPLACE = {0x104, 0x106, 0x163}
            self.FIXED_WEATHER_ENTDS = [0x133, 0x17b, 0x163]
            self.GARILAND = 3
            self.ENDING = 0x7c
            self.MUROND_HOLY_PLACE = 0x70
            return

        self.NO_REPLACE = {0x184, 0x185, 0x1c2}
        self.FIXED_WEATHER_ENTDS = [0x19f, 0x1b5, 0x1c2]
        self.GARILAND = 9
        self.ENDING = 0x12b
        self.MUROND_HOLY_PLACE = 0x1b2

    @classproperty
    def after_order(self):
        return [GNSObject, UnitObject]

    @classproperty
    def randomize_order(self):
        return sorted(self.every, key=lambda e: e.signature)

    @cached_property
    def canonical_relative(self):
        if self.old_data['entd_index'] == 0:
            return self
        for e in EncounterObject.every:
            if e.old_data['entd_index'] == self.old_data['entd_index']:
                return e

    @property
    def name(self):
        return 'ENC {0:0>3X} ENTD {1:0>3X} MAP {2:0>3}'.format(
            self.index, self.entd_index, self.old_data['map_index'])

    @property
    def is_replaceable(self):
        if self.entd_index in self.NO_REPLACE:
            return False
        if 'bigtide' in get_activated_codes():
            return (self.num_characters
                        and not hasattr(self.map, '_loaded_from'))
        return (self.num_characters and not self.has_walktos
                    and not hasattr(self.map, '_loaded_from'))

    @cached_property
    def is_canonical(self):
        return self.canonical_relative is self

    @property
    def map(self):
        return GNSObject.get_by_map_index(self.map_index)

    @property
    def conditional(self):
        return BattleConditionalObject.get(self.conditional_index)

    def get_unit_by_id(self, unit_id):
        for u in self.units:
            if u.unit_id == unit_id:
                return u

    def get_movements(self, codes=None):
        def get_last_coordinates(coord_dict, unit_id):
            if coord_dict[unit_id]:
                return coord_dict[unit_id][-1]
            else:
                unit = self.get_unit_by_id(unit_id)
                if unit:
                    return (unit.old_data['x'], unit.old_data['y'])
            return None, None

        if codes is None:
            codes = (0x28, 0x47, 0x5f, 0x3b)
        movements = {}
        if self.conditional_index > 0:
            for i, v in enumerate(self.conditional.events):
                v_movements = defaultdict(list)
                for (code, parameters) in v.instructions:
                    if code not in codes:
                        continue
                    unit_id, x, y = None, None, None
                    if code in {0x28, 0x5f} & set(codes):
                        unit_id = parameters[0]
                        x, y = parameters[2], parameters[3]
                    elif code == 0x47 and code in codes:
                        unit_id = parameters[2]
                        x, y = parameters[3], parameters[4]
                    elif code == 0x3b and code in codes:
                        unit_id = parameters[0]
                        relx, rely = parameters[2], parameters[4]
                        if relx & 0x8000:
                            relx = 0x10000 - relx
                        if rely & 0x8000:
                            rely = 0x10000 - rely
                        relx = int(round(relx / 0x28))
                        rely = int(round(rely / 0x28))
                        if relx == rely == 0:
                            continue

                        if i > 0 and not v_movements[unit_id]:
                            old_x, old_y = get_last_coordinates(movements[i-1],
                                                                unit_id)
                        else:
                            old_x, old_y = get_last_coordinates(v_movements,
                                                                unit_id)
                        if old_x is not None:
                            x, y = (old_x + relx, old_y + rely)
                        else:
                            self._protected = True
                        unit = self.get_unit_by_id(unit_id)
                        if unit and not v_movements[unit_id]:
                            unit._fixed_initial_coordinates = True

                    if None not in (unit_id, x, y):
                        assert parameters[1] == 0
                        old_x, old_y = get_last_coordinates(v_movements,
                                                            unit_id)
                        if x == old_x and y == old_y:
                            continue

                        unit = self.get_unit_by_id(unit_id)
                        if unit and code in {0x28, 0x3b}:
                            unit._is_walking_unit = True

                        v_movements[unit_id].append((x, y))

                movements[i] = v_movements
        return movements

    @cached_property
    def movements(self):
        encs = [e for e in EncounterObject.every
                if e.old_data['map_index'] == self.old_data['map_index']]
        movements = defaultdict(set)
        for e in encs:
            e_movementss = e.get_movements()
            if not e_movementss:
                continue
            for e_movements in e_movementss.values():
                for u in e_movements:
                    movements[u] |= set(e_movements[u])
        return movements

    @cached_property
    def walktos(self):
        encs = [e for e in EncounterObject.every
                if e.old_data['map_index'] == self.old_data['map_index']]
        movements = defaultdict(set)
        for e in encs:
            e_movementss = e.get_movements(codes=(0x28, 0x3b))
            if not e_movementss:
                continue
            for e_movements in e_movementss.values():
                for u in e_movements:
                    movements[u] |= set(e_movements[u])
        return movements

    @cached_property
    def has_walktos(self):
        for u in self.walktos:
            if len(self.walktos[u]) > 0:
                return True
        return False

    @cached_property
    def has_special_walktos(self):
        for u in self.walktos:
            if 1 <= u <= 0x7f and len(self.walktos[u]) > 0:
                return True
        return False

    @cached_property
    def has_movements(self):
        return any(coordinates for coordinates in self.movements.values())

    @cached_property
    def has_special_movements(self):
        for u in self.movements:
            if 1 <= u <= 0x7f and self.movements[u]:
                return True
        return False

    @cached_property
    def formations(self):
        return [FormationObject.get(f) for f in self.formation_indexes if f]

    @property
    def old_formations(self):
        return [FormationObject.get(f) for f in
                self.old_data['formation_indexes'] if f]

    @property
    def num_characters(self):
        return sum([f.num_characters for f in self.old_formations])

    @property
    def entd(self):
        return ENTDObject.get(self.entd_index)

    @property
    def units(self):
        return self.entd.units

    @classmethod
    def get_unused(self):
        candidates = [
            e for e in EncounterObject.every if e.map_index == 0 and
            e.conditional_index == 0 and e.entd_index == 0
            and e.next_scene == 0 and e.following == 0 and e.scenario == 0]
        unused = candidates[0]
        unused.scenario = max(e.scenario for e in EncounterObject.every) + 1
        return unused

    @classmethod
    def get_by_scenario(self, scenario):
        encs = [e for e in EncounterObject.every if e.scenario == scenario]
        if len(encs) == 1:
            return encs[0]

    @property
    def family(self):
        if self.scenario == 0 or self.entd_index == 0:
            return [self]

        family = [e for e in EncounterObject.every
                  if e.entd_index == self.entd_index]
        assert len({e.conditional_index for e in family
                    if e.conditional_index > 0}) <= 1
        assert len({wco for e in family for wco in e.world_conditionals}) <= 1

        return family

    @property
    def world_conditionals(self):
        return [wco for wco in WorldConditionalObject.every
                if self in wco.encounters]

    def set_formations(self, f1, f2=0):
        f1 = f1.index
        f2 = f2.index if f2 else f2
        self.formation_indexes = [f1, f2]
        self.clear_cache()
        for f in self.old_data['formation_indexes']:
            f = FormationObject.get(f)
            f.clear_cache()

    def set_occupied(self):
        for u, coordinates in self.movements.items():
            for (x, y) in coordinates:
                self.map.set_occupied(x, y)
        for u in self.units:
            if (hasattr(u, '_fixed_initial_coordinates')
                    and u._fixed_initial_coordinates):
                self.map.set_occupied(u.old_data['x'], u.old_data['y'])
        if self.has_movements and 'bigtide' not in get_activated_codes():
            for u in self.units:
                if (u.unit_id in self.movements
                        and u.get_bit('always_present')):
                    self.map.set_occupied(u.old_data['x'], u.old_data['y'])
                    continue

    def read_data(self, filename=None, pointer=None):
        if not hasattr(EncounterObject, 'GARILAND'):
            EncounterObject.set_class_constants()
        super().read_data(filename, pointer)

    def preprocess(self):
        self.set_occupied()
        if (self.index == self.MUROND_HOLY_PLACE
                and self.formation_indexes == [232, 324]):
            # Murond Holy Place typo correction
            self.formation_indexes = [323, 324]
            self.old_data['formation_indexes'] = self.formation_indexes
            self.clear_cache()

    def is_map_movement_compatible(self, c):
        movement_tiles = {(x, y) for u in self.movements
                          for (x, y) in self.movements[u]}
        movement_tiles |= {
            (u.x, u.y) for u in self.units
            if hasattr(u, '_fixed_initial_coordinates')}
        gns = GNSObject.get_by_map_index(c)
        valid_tiles = set(
            gns.get_tiles_compare_attribute('bad_regardless', False))
        return valid_tiles >= movement_tiles

    def replace_map(self):
        if not self.is_replaceable:
            return

        if (random.random() > self.random_degree ** 0.25
                and 'novanilla' not in get_activated_codes()):
            return

        candidates = [map_index for map_index in self.REPLACING_MAPS
                      if map_index not in self.DONE_MAPS]
        if not candidates:
            candidates = [map_index for map_index in sorted(self.REPLACED_MAPS)
                          if map_index not in self.DONE_MAPS]

        if self.has_movements:
            candidates = [c for c in candidates
                          if self.is_map_movement_compatible(c)]

        if not candidates:
            return

        chosen = random.choice(candidates)
        self.map_index = chosen
        self.DONE_MAPS.add(chosen)
        self.REPLACED_MAPS.add(self.old_data['map_index'])

    def generate_formations(self, num_characters=None):
        if num_characters is None:
            num_characters = self.num_characters
        templates = [e for e in EncounterObject.every if e.formations]
        template = random.choice(templates)
        num_formations = len(template.old_formations)
        if num_characters == 0:
            return
        assert 1 <= num_formations <= 2
        if num_characters > 1 and num_formations == 2:
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

        units = list(self.units)
        random.shuffle(units)
        for u in units:
            if hasattr(u, '_fixed_initial_coordinates'):
                assert u._fixed_initial_coordinates
                assert u.x == u.old_data['x']
                assert u.y == u.old_data['y']
                self.map.set_occupied(u.x, u.y)

        for u in units:
            if hasattr(u, '_fixed_initial_coordinates'):
                continue
            if u.is_present:
                u.find_appropriate_position()

    def randomize_music(self, prefer_dummied=False):
        if self.num_characters == 0:
            return

        if prefer_dummied:
            candidates = sorted(self.DUMMIED_SONGS)
        else:
            candidates = sorted(self.CANDIDATE_SONGS)
            if random.randint(1, 100) == 100:
                candidates.append(35)

        temp = [c for c in candidates if c not in EncounterObject.used_music]
        if temp:
            candidates = temp
        else:
            EncounterObject.used_music = set()

        self.music = [m if m in self.FIXED_SONGS else random.choice(candidates)
                      for m in self.music]
        EncounterObject.used_music |= set(self.music)

    def randomize_weather(self):
        if self.entd_index in self.FIXED_WEATHER_ENTDS:
            return

        if self.weather <= 4:
            if random.randint(1, 7) == 7:
                self.night = 1
            else:
                self.night = 0
            if random.randint(1, 4) == 4:
                self.weather = random.choice([1, 2, 3, 4])
            else:
                self.weather = 0

    def randomize(self):
        if self.old_data['entd_index'] == 0:
            return

        if self.is_canonical:
            for u in self.units:
                if (u.unit_id in self.movements
                        and u.is_important_map_movements
                        and 'bigtide' not in get_activated_codes()
                        and u.unit_id in self.get_movements()[0]
                        and hasattr(u, '_is_walking_unit')
                        and u._is_walking_unit):
                    u._fixed_initial_coordinates = True
            self.replace_map()
            self.reseed('formations')
            self.generate_formations()
        self.randomize_weather()

    def cleanup(self):
        for attr in ['music', 'weather', 'night',
                'formation_indexes', 'map_index']:
            if self.old_data[attr] == self.canonical_relative.old_data[attr]:
                setattr(self, attr, getattr(self.canonical_relative, attr))
        if not self.is_canonical:
            self.clear_cache()

        old_spritecount = len(self.entd.old_sprites) + self.num_characters
        new_spritecount = len(self.entd.sprites) + self.num_characters
        assert new_spritecount <= max(old_spritecount, 9)

        for f in self.formations:
            assert f.map_index == self.map_index


class MusicObject(TableObject):
    flag = 'c'
    flag_description = 'battle music'
    custom_random_enable = flag

    def randomize(self):
        EncounterObject.get(self.index).randomize_music()


class ConditionalMixin(TableObject):
    @classmethod
    def get_instruction(self, f):
        instruction = []
        while True:
            code = int.from_bytes(f.read(2), byteorder='little')
            num_parameters = self.NUM_PARAMETERS[code]
            parameters = tuple(int.from_bytes(f.read(2), byteorder='little')
                               for _ in range(num_parameters))
            instruction.append((code, parameters))
            if code in self.TERMINATING_CODES:
                break
        return instruction

    @classmethod
    def instruction_to_bytes(self, instruction):
        sequence = []
        for code, parameters in instruction:
            sequence.append(code)
            for p in parameters:
                sequence.append(p)
        return b''.join(c.to_bytes(2, byteorder='little') for c in sequence)

    @property
    def pretty(self):
        s = self.description + '\n'
        for instruction in self.instructions:
            line = ''
            for code, parameters in instruction:
                parameters = ','.join('{0:0>4x}'.format(p) for p in parameters)
                line += '{0:0>2X}:{1}  '.format(code, parameters)
            s += line + '\n'
        return s.strip()

    def preprocess_tlw(self):
        f = get_open_file(self.filename)
        instructions = []
        start_pointer = self.BASE_POINTER + self.instructions_pointer
        f.seek(start_pointer)
        start_pointer = (self.BASE_POINTER
                         + int.from_bytes(f.read(2), byteorder='little'))
        try:
            successor = self.get(self.index+1)
            end_pointer = successor.BASE_POINTER + successor.instructions_pointer
            f.seek(end_pointer)
            end_pointer = (successor.BASE_POINTER
                           + int.from_bytes(f.read(2), byteorder='little'))
        except KeyError:
            end_pointer = None
        f.seek(start_pointer)
        instructions = []
        while True:
            pointer = f.tell()
            if end_pointer is not None:
                if pointer > end_pointer:
                    raise Exception(
                        'Exceeded instruction space: {0:x}'.format(pointer))
                if pointer == end_pointer:
                    break
            else:
                peek = f.read(2)
                if peek == b'\x00\x00':
                    break
                f.seek(pointer)
            instructions.append(self.get_instruction(f))
        self.instructions = instructions

    def preprocess(self):
        if get_global_label() == 'FFT_TLW' and isinstance(self, BattleConditionalObject):
            return self.preprocess_tlw()

        f = get_open_file(self.filename)
        instructions = []
        while True:
            f.seek(self.BASE_POINTER + self.instructions_pointer
                   + (2*len(instructions)))
            instruction_pointer = int.from_bytes(f.read(2), byteorder='little')
            if instruction_pointer == 0:
                break
            f.seek(self.BASE_POINTER + instruction_pointer)
            peek = f.read(2)
            if peek == b'\x00\x00':
                break
            f.seek(self.BASE_POINTER + instruction_pointer)
            instructions.append(self.get_instruction(f))
        self.instructions = instructions

    @classmethod
    def write_all(self, filename):
        pointer_address = self.BASE_POINTER + (2*len(self.every))
        num_total_instructions = sum(len(c.instructions)+1 for c in self.every)
        instructions_address = pointer_address + (2*num_total_instructions)
        pointer_offset = 0
        instructions_offset = 0
        f = get_open_file(self.get(0).filename)
        for c in self.every:
            c.instructions_pointer = (pointer_address + pointer_offset
                                      - self.BASE_POINTER)
            for i in c.instructions:
                f.seek(pointer_address + pointer_offset)
                ipointer = instructions_address + instructions_offset
                ip = (ipointer-self.BASE_POINTER)
                f.write(ip.to_bytes(2, byteorder='little'))

                pointer_offset += 2

                f.seek(ipointer)
                data = self.instruction_to_bytes(i)
                f.write(data)
                instructions_offset += len(data)
            f.seek(pointer_address + pointer_offset)
            f.write(b'\x00\x00')
            pointer_offset += 2

        assert max(c.pointer for c in self.every) <= pointer_address - 2
        assert pointer_address + pointer_offset <= instructions_address
        assert (instructions_address + instructions_offset <= self.END_ADDRESS)
        super().write_all(filename)

    def load_patch(self, patch):
        new_instructions = []
        for line in patch.split('\n'):
            instruction = []
            for codepa in line.split():
                code, parameters = codepa.split(':')
                code = int(code, 0x10)
                parameters = [int(p, 0x10) for p in parameters.split(',') if p]
                assert len(parameters) == self.NUM_PARAMETERS[code]
                instruction.append((code, parameters))
            new_instructions.append(instruction)

        self.instructions = new_instructions


class BattleConditionalObject(ConditionalMixin):
    BASE_POINTER = 0x14938
    END_ADDRESS = 0x16af4

    TERMINATING_CODES = {0x19}

    NUM_PARAMETERS = {
        0x01: 2,
        0x02: 2,
        0x03: 2,
        0x04: 1,
        0x05: 2,
        0x06: 2,
        0x07: 2,
        0x08: 2,
        0x09: 2,
        0x0a: 2,
        0x0b: 1,
        0x0d: 1,
        0x0e: 2,
        0x0f: 2,
        0x10: 3,
        0x11: 3,
        0x12: 2,
        0x13: 2,
        0x16: 0,
        0x18: 4,
        0x19: 1,
        0x25: 4,
        }

    DD_END_EVENT = 0x25

    @property
    def event_indexes(self):
        event_indexes = []
        for instruction in self.instructions:
            code, parameters = instruction[-1]
            assert code == 0x19
            assert len(parameters) == 1
            event_indexes.append(parameters[0])
        return event_indexes

    @property
    def events(self):
        return [EventObject.get(i) for i in self.event_indexes]


class WorldConditionalObject(ConditionalMixin):
    BASE_POINTER = 0x30234
    END_ADDRESS = 0x31238

    TERMINATING_CODES = {0x19, 0x1a, 0x1d, 0x1e, 0x1f,
                         0x20, 0x21, 0x22, 0x23, 0x24}

    NUM_PARAMETERS = {
        0x01: 2,
        0x02: 2,
        0x03: 2,
        0x04: 1,
        0x0e: 1,
        0x0f: 1,
        0x10: 2,
        0x11: 2,
        0x12: 1,
        0x13: 1,
        0x19: 2,
        0x1a: 8,
        0x1c: 2,
        0x1d: 1,
        0x1e: 3,
        0x1f: 2,
        0x20: 2,
        0x21: 2,
        0x22: 1,
        0x23: 1,
        0x24: 1,
        0x25: 1,
        0x26: 1,
        0x27: 1,
        0x28: 1,
        }

    WARJILIS = 0xc
    ZARGHIDAS = 0xe

    @classproperty
    def after_order(self):
        return [UnitObject]

    @property
    def encounters(self):
        scenario_indexes = []
        for instruction in self.instructions:
            code, parameters = instruction[-1]
            if code == 0x19:
                scenario_indexes.append(parameters[0])
            elif code == 0x1a:
                scenario_indexes.extend([parameters[i] for i in (1, 3, 5, 7)])
            elif code == 0x1e:
                scenario_indexes.append(parameters[1])

        return [EncounterObject.get_by_scenario(i) for i in scenario_indexes]

    def insert_bonus(self, map_index, monsters, initial_encounter=0):
        before = self.encounters[initial_encounter]

        gariland = EncounterObject.get(EncounterObject.GARILAND)
        new_encounter = EncounterObject.get_unused()
        new_entd = ENTDObject.get_unused()
        scenario = new_encounter.scenario
        new_encounter.copy_data(gariland)
        new_encounter.scenario = scenario
        new_encounter.conditional_index = BattleConditionalObject.DD_END_EVENT
        new_encounter.map_index = map_index
        new_encounter.ramza = 0
        new_encounter.randomize_music(prefer_dummied=True)
        new_encounter.randomize_weather()
        new_encounter.entd_index = new_entd.index

        for u in new_encounter.units:
            u.reset_blank()

        special_templates =[
            u for u in UnitObject.special_unit_pool
            if u.is_human and u.has_unique_name and u.is_human_old]
        partner_template = random.choice(special_templates)
        special_templates = [
            u for u in special_templates if
            u.character_name != partner_template.character_name]
        partner = new_encounter.units[0]
        partner.become_another(partner_template)
        for bitflag in [
                'save_formation', 'test_teta', 'load_formation',
                'join_after_event', 'control', 'enemy_team','alternate_team',
                'randomly_present']:
            partner.set_bit(bitflag, False)
        partner.set_bit('hidden_stats', True)
        partner.set_bit('immortal', True)
        partner.level = random.randint(random.randint(50, 99), 99)
        partner.righthand = ItemObject.CHAOS_BLADE
        partner.head = ItemObject.RIBBON
        partner.body = ItemObject.REFLECT_MAIL
        partner.secondary = 0xfe
        partner.lefthand = 0xfe
        partner.support = AbilityObject.MAINTENANCE

        pinatas = new_encounter.units[1:-1]
        assert len(set([partner] + pinatas)) == 15

        if monsters:
            sprite_pool = set()
            monster_jobs = [
                j for j in JobObject.every if j.index in JobObject.MONSTER_JOBS
                and j.monster_sprite > 0]
            sprite_pool = random.sample(
                sorted({j.monster_portrait for j in monster_jobs}), 7)

            monster_jobs = [
                j for j in JobObject.every if j.index in JobObject.MONSTER_JOBS
                and j.monster_sprite > 0 and j.monster_portrait in sprite_pool]
            monster_jobs = random.sample(monster_jobs, len(pinatas))

            for p, j in zip(pinatas, monster_jobs):
                p.graphic = UnitObject.MONSTER_GRAPHIC
                p.job_index = j.index
                p.palette = 3
                p.secondary = 0
                for attr in UnitObject.EQUIPMENT_ATTRS:
                    setattr(p, attr, 0)
                p.set_bit('monster', True)
        else:
            chosen = random.choice(special_templates)
            jobs = random.sample(JobObject.ranked_generic_jobs_candidates,
                                 len(pinatas)-1)
            jobs.append(chosen.job)
            for p, j in zip(pinatas, jobs):
                p.graphic = chosen.graphic
                p.job_index = j.index
                if p.job is chosen.job:
                    for attr in ['month', 'day', 'brave', 'faith',
                                 'name_index']:
                        setattr(p, attr, getattr(chosen, attr))
                else:
                    p.unlocked = p.job_index - JobObject.SQUIRE_INDEX
                    p.unlocked_level = random.randint(0, 8)

                for attr in UnitObject.EQUIPMENT_ATTRS:
                    setattr(p, attr, 0xff)

                good_item_attr = random.choice(UnitObject.EQUIPMENT_ATTRS)
                if good_item_attr in ['righthand', 'lefthand']:
                    candidates = ItemObject.ranked_hands_candidates
                else:
                    candidates = ItemObject.ranked_nohands_candidates

                max_index = len(candidates) - 1
                value = mutate_normal(0.5, 0, 1.0, return_float=True,
                                      random_degree=PoachObject.random_degree)
                index = int(round(value * max_index))
                good_item = candidates[index]
                if good_item.get_bit('weapon'):
                    bad_item_attr = random.choice([
                        equip for equip in UnitObject.EQUIPMENT_ATTRS
                        if equip != good_item_attr])
                else:
                    if good_item_attr == 'righthand':
                        bad_item_attr = 'lefthand'
                    else:
                        bad_item_attr = 'righthand'

                setattr(p, good_item_attr, good_item.index)
                setattr(p, bad_item_attr, 0xfe)
                p.set_bit(chosen.get_gender(), True)

        partner.clear_cache()
        for p in pinatas:
            p.level = random.randint(1, random.randint(1, 50))
            p.set_bit('enemy_team', True)
            p.set_bit('always_present', True)
            p.set_bit('control', True)
            p.clear_cache()

        new_encounter.clear_cache()
        new_encounter.generate_formations(num_characters=1)

        for encounter in before.family:
            if encounter.following == 0x80:
                encounter.following = 0x81
                encounter.next_scene = new_encounter.scenario


class UnitNameObject(TableObject):
    CUSTOM_NAMES_FILEPATH = path.join('custom', 'unit_names.txt')
    try:
        custom_names = read_lines_nocomment(CUSTOM_NAMES_FILEPATH)
    except FileNotFoundError:
        print('WARNING: File not found - %s' % CUSTOM_NAMES_FILEPATH)
        custom_names = []

    CHARTABLE = dict(
        list(enumerate(digits + ascii_uppercase + ascii_lowercase))
        + [(0xfa, ' '), (0xd9, '~'), (0xb6, '.'), (0xc1, "'")])
    for (k, v) in sorted(CHARTABLE.items()):
        assert v not in CHARTABLE
        CHARTABLE[v] = k

    done_names = set()

    @clached_property
    def valid_name_lengths(self):
        return {len(u.old_namestr) for u in UnitNameObject.every}

    @clached_property
    def candidate_names(self):
        def remove_char(name):
            removables = [i for (i, c) in enumerate(name)
                          if 1 <= i <= len(name)-2 and c.lower() in "aeiou"]
            if not removables:
                return name[:-1]
            i = random.choice(removables)
            name = name[:i] + name[i+1:]
            return name

        invalid_names = {name for name in UnitNameObject.custom_names
                         if len(name) not in UnitNameObject.valid_name_lengths}
        revised_names = {}
        for invalid_name in sorted(invalid_names):
            name = invalid_name
            if len(name) < min(UnitNameObject.valid_name_lengths):
                continue
            while len(name) not in UnitNameObject.valid_name_lengths:
                name = remove_char(name)
            revised_names[invalid_name] = name

        invalid_names = {i for i in invalid_names if i not in revised_names}
        valid_names = [name for name in UnitNameObject.custom_names
                       if name not in invalid_names]
        valid_names = [revised_names[name] if name in revised_names else name
                       for name in valid_names]

        return valid_names

    @clached_property
    def candidate_names_by_length(self):
        by_length = defaultdict(list)
        for name in self.candidate_names:
            by_length[len(name)].append(name)
        return by_length

    @cached_property
    def canonical_relative(self):
        for u in UnitNameObject.every:
            if u.old_namestr == self.old_namestr:
                return u

    @cached_property
    def is_canonical(self):
        return self.canonical_relative is self

    @property
    def name(self):
        if not self.is_canonical:
            return self.canonical_relative.name

        namestr = (self.new_namestr if hasattr(self, 'new_namestr')
                   else self.old_namestr)
        return ''.join(self.CHARTABLE[c] for c in namestr)

    def read_data(self, filename=None, pointer=None):
        super().read_data(filename, pointer)
        self.old_namestr = b''
        f = get_open_file(self.filename)
        f.seek(self.pointer)
        while True:
            c = f.read(1)
            if c == b'\xfe':
                break
            self.old_namestr += c

    def write_data(self, filename=None, pointer=None):
        super().write_data(filename, pointer)

        if hasattr(self.canonical_relative, 'new_namestr'):
            new_namestr = self.canonical_relative.new_namestr
            assert len(new_namestr) == len(self.old_namestr)
            f = get_open_file(self.filename)
            f.seek(self.pointer)
            f.write(new_namestr)

    def set_name(self, name):
        old_name = name
        name = name.replace('_', ' ')
        if name == name.lower():
            name = ' '.join([w[0].upper() + w[1:] if w else w
                             for w in name.split(' ')])
        name = bytes([self.CHARTABLE[c] for c in name])
        assert len(name) == len(old_name)
        self.new_namestr = name

    def randomize(self):
        if not self.is_canonical:
            return

        candidates = [name for name in
                      self.candidate_names_by_length[len(self.old_namestr)]
                      if name not in UnitNameObject.done_names]
        if not candidates:
            return

        max_index = len(candidates)-1
        index = random.randint(0, random.randint(0, max_index))
        chosen = candidates[index]
        self.set_name(chosen)
        UnitNameObject.done_names.add(chosen)


class PropositionObject(TableObject):
    def cleanup(self):
        if 1 <= self.unlocked <= 5:
            self.unlocked = 1


class PropositionJPObject(TableObject): pass


class EventObject(TableObject):
    PARAMETER_FILENAME = path.join(tblpath, 'parameters_events.txt')
    PARAMETERS = {}
    for line in read_lines_nocomment(PARAMETER_FILENAME):
        if ':' in line:
            code, parameters = line.split(':')
            if parameters:
                parameters = tuple(map(int, parameters.split(',')))
            else:
                parameters = ()
        else:
            code, parameters = line, ()
        code = int(code, 0x10)
        PARAMETERS[code] = parameters

    @classproperty
    def ENDING_SCENES(self):
        if get_global_label() == 'FFT_TLW':
            return (0x7d, 0x7c)
        else:
            return (0x12c, 0x147)

    @classmethod
    def data_to_instructions(self, data):
        instructions = []
        while data:
            code, data = data[0], data[1:]
            parameter_sizes = self.PARAMETERS[code]
            parameters = []
            for s in parameter_sizes:
                value, data = data[:s], data[s:]
                assert len(value) == s
                value = int.from_bytes(value, byteorder='little')
                parameters.append(value)
            instructions.append((code, parameters))
            if code == 0xdb:
                break
        return instructions

    @classmethod
    def data_to_messages(self, data):
        messages = data.split(b'\xfe')
        return messages[:-1]

    @cached_property
    def encounters(self):
        return [e for e in EncounterObject.every
                if e.conditional_index > 0
                and self.index in e.conditional.event_indexes]

    @cached_property
    def units(self):
        return [u for e in self.encounters for u in e.units]

    @property
    def instruction_data(self):
        data = b''
        for code, parameters in self.instructions:
            data += code.to_bytes(1, byteorder='little')
            parameter_sizes = self.PARAMETERS[code]
            assert len(parameters) == len(parameter_sizes)
            for psize, p in zip(parameter_sizes, parameters):
                data += p.to_bytes(psize, byteorder='little')
        return data

    @cached_property
    def is_initial_event(self):
        for bco in BattleConditionalObject.every:
            if self.index == bco.event_indexes[0]:
                return True
        return False

    @property
    def message_data(self):
        if hasattr(self, 'new_messages'):
            messages = self.new_messages
        else:
            messages = self.messages
        data = b'\xfe'.join(messages)
        if data:
            data += b'\xfe'
        return data

    @property
    def pretty(self):
        s = self.description + '\n'
        for i, (code, parameters) in enumerate(self.instructions):
            s += '{0:>3}. {1:0>2X}:'.format(i, code)
            parameter_sizes = self.PARAMETERS[code]
            for psize, p in zip(parameter_sizes, parameters):
                s += ('{0:0>%sx},' % (psize*2)).format(p)
            s = s.rstrip(',')
            s += '\n'
        return s.strip()

    @property
    def message_indexes(self):
        indexes = []
        for code, parameters in self.instructions:
            if code == 0x10:
                assert parameters[0] == 0x10
                indexes.append(parameters[2])
            elif code == 0x51:
                index = parameters[1]
                if index != 0xffff:
                    indexes.append(parameters[1])
        if indexes:
            if max(indexes) > len(self.messages):
                self._no_modify = True
            assert min(indexes) >= 1
        return indexes

    def read_data(self, filename=None, pointer=None):
        super().read_data(filename, pointer)

        f = get_open_file(self.filename)
        f.seek(self.pointer)
        text_offset = int.from_bytes(f.read(4), byteorder='little')
        if get_global_label() == 'FFT_TLW':
            max_text_offset = 0x2000
            #if text_offset < max_text_offset:
            #    max_text_offset = ((text_offset // 0x800) * 0x800)
            #    if not text_offset % 0x800:
            #        max_text_offset += 0x800
            #max_text_offset = max(max_text_offset, 0x1800)
        else:
            max_text_offset = 0x1800
        if text_offset >= max_text_offset:
            assert text_offset == 0xf2f2f2f2
            assert get_global_label() != 'FFT_TLW'
        length = min(text_offset, max_text_offset) - 4
        event_data = f.read(length)
        length = max_text_offset - (length + 4)
        text_data = f.read(length)

        f.seek(self.pointer + max_text_offset)
        value = int.from_bytes(f.read(4), byteorder='little')
        if value != 0xf2f2f2f2:
            self._no_modify = True

        self.old_text_offset = text_offset
        self.instructions = self.data_to_instructions(event_data)
        self.messages = self.data_to_messages(text_data)
        assert self.instruction_data == event_data[:len(self.instruction_data)]
        assert self.message_data == text_data[:len(self.message_data)]
        if self.message_indexes and text_offset >= max_text_offset:
            raise Exception('Undefined messages.')

    def automash(self):
        if self.index in self.ENDING_SCENES:
            return

        for i in range(len(self.instructions)):
            code, parameters = self.instructions[i]
            if code == 0x10:
                parameters = list(parameters)
                assert parameters[0] == 0x10
                message_index = parameters[2]
                try:
                    message = self.messages[message_index-1]
                except IndexError:
                    continue
                if b'\xfb' in message and b'\xfc' in message:
                    continue
                box_type = parameters[1]
                box_type &= 0x8f
                parameters[1] = box_type
                self.instructions[i] = (code, tuple(parameters))

    def cull_messages(self):
        if hasattr(self, '_no_modify') and self._no_modify:
            return
        dummy_message = b'\x36\x2c\x31'
        indexes = self.message_indexes
        self.new_messages = []
        for i in range(len(self.messages)):
            if (i+1) not in indexes:
                self.new_messages.append(dummy_message)
            else:
                self.new_messages.append(self.messages[i])

    def preprocess(self):
        self.cull_messages()

    def load_patch(self, patch):
        if hasattr(self, '_no_modify') and self._no_modify:
            raise Exception('Cannot patch event %X.' % self.index)

        old = self.pretty

        removals = [line for line in patch.split('\n')
                    if line[0] == '-']
        additions = [line for line in patch.split('\n')
                     if line[0] == '+']

        removal_indexes = set()
        for r in removals:
            assert r[1:] in old
            index, _ = r[1:].strip().split('.')
            index = int(index)
            removal_indexes.add(index)

        new_instructions = [inst for (i, inst) in enumerate(self.instructions)
                            if i not in removal_indexes]

        for a in additions:
            index, s = a[1:].strip().split('.')
            index = int(index)
            s = s.strip()
            code, parameters = s.split(':')
            code = int(code, 0x10)
            parameters = [int(p, 0x10) for p in parameters.split(',') if p]
            assert len(parameters) == len(self.PARAMETERS[code])
            new_instructions.insert(index, (code, parameters))

        self.instructions = new_instructions

    def setup_chocobo_knights(self):
        if not self.is_initial_event:
            return

        riders = [u for u in self.units if hasattr(u, '_chocobo_mount')]
        mounts = [u for u in self.units if hasattr(u, '_chocobo_rider')]
        assert len(riders) == len(mounts)
        if not riders:
            return
        next_unit_id = 0x90
        mount_instructions = []
        for rider in riders:
            mount = [m for m in mounts if m._chocobo_rider is rider][0]
            assert rider._chocobo_mount is mount
            assert mount.get_bit('always_present')
            if rider.unit_id == 0xff:
                rider.unit_id = next_unit_id
                next_unit_id += 1
            elevation = 1 if mount.is_upper else 0
            x, y = rider.full_movement_path[-1]
            instruction = (0x5f, (rider.unit_id, 0x00, x, y,
                                  elevation, mount.facing))
            mount_instructions.append(instruction)
            instruction = (0x5f, (mount.unit_id, 0x00, mount.x, mount.y,
                                  elevation, mount.facing))
            mount_instructions.append(instruction)
            instruction = (0x28, (rider.unit_id, 0x00, mount.x, mount.y,
                                  elevation, 0x00, 0x7f, 0x01))
            mount_instructions.append(instruction)
            instruction = (0x29, (rider.unit_id, 0x00))
            mount_instructions.append(instruction)
        assert self.instructions[-1] == (0xdb, [])
        self.instructions = (self.instructions[:-1] + mount_instructions
                             + [self.instructions[-1]])
        assert self.instructions[-1] == (0xdb, [])

    def cleanup(self):
        if 'automash_dialogue.txt' in get_activated_patches():
            self.automash()
        self.setup_chocobo_knights()

    def write_data(self, filename=None, pointer=None):
        if self.old_text_offset == 0xf2f2f2f2 and self.messages:
            raise Exception('Event %X cannot have messages.' % self.index)

        no_modify = hasattr(self, '_no_modify') and self._no_modify
        length = len(self.instruction_data) + 4
        f = get_open_file(self.filename)
        if self.old_text_offset != 0xf2f2f2f2 and not no_modify:
            f.seek(self.pointer)
            f.write(length.to_bytes(4, byteorder='little'))

        f.seek(self.pointer + 4)
        f.write(self.instruction_data)

        if no_modify:
            return

        free_space = 0x1800 - length
        message_data = self.message_data
        if len(message_data) > free_space:
            raise Exception('Not enough space.')
        if len(message_data) < free_space:
            message_data = message_data + (
                b'\x00' * (free_space - len(message_data)))
        assert len(message_data) == free_space
        f.write(message_data)


class MapMixin(TableObject):
    @cached_property
    def map_index(self):
        filename = path.split(self.filename)[-1]
        base, extension = filename.split('.')
        return int(base[-3:])

    @property
    def gns(self):
        return GNSObject.get(self.map_index)

    @classmethod
    def get_by_map_index(self, map_index):
        if not hasattr(self, '_map_index_cache'):
            self._map_index_cache = {}
        if map_index in self._map_index_cache:
            return self._map_index_cache[map_index]

        result = [m for m in self.every if m.map_index == map_index]
        if len(result) == 1:
            result = result[0]
        else:
            result = None

        self._map_index_cache[map_index] = result
        return self.get_by_map_index(map_index)

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
            self.clear_cache()
            self.gns.clear_cache()
            self._loaded_from = filename

        for e in EncounterObject.every:
            if e.map_index == self.map_index:
                e.set_occupied()

    def write_data(self, filename=None, pointer=None):
        if hasattr(self, '_is_removed') and self._is_removed:
            return
        f = get_open_file(self.filename)
        f.write(self.data)


class GNSPointerObject(TableObject):
    @property
    def is_free(self):
        return self.sector == 0

    def preprocess(self):
        new_filenames = set()
        if self.is_free and GNSObject.WILDCARD_MAP_OPTIONS:
            chosen = random.choice(GNSObject.WILDCARD_MAP_OPTIONS)

            replacing_filenames, template_index = chosen

            new_filenames = set()
            new_gns_filename = None
            textures, meshes = [], []
            template_basename = 'MAP{0:0>3}'.format(template_index)
            for template in sorted(listdir(path.join(SANDBOX_PATH, 'MAP'))):
                if template.startswith(template_basename):
                    extension = template.split('.')[-1]
                    old_filename = path.join(
                        SANDBOX_PATH, 'MAP', template)
                    new_filename = path.join(
                        SANDBOX_PATH, 'MAP',
                        'RND{0:0>3}.{1}'.format(self.index, extension))
                    assert new_filename not in new_filenames
                    new_filenames.add(new_filename)
                    for rfn in replacing_filenames:
                        head, tail = path.split(rfn)
                        if tail == template:
                            copyfile(rfn, new_filename)
                            break
                    else:
                        copyfile(old_filename, new_filename)

                    filesize = stat(new_filename).st_size
                    if extension == 'GNS':
                        new_gns_filename = new_filename
                    elif filesize == 0x20000:
                        txo = TextureObject.create_new(filename=new_filename)
                        txo._loaded_from = old_filename
                        textures.append(txo)
                    else:
                        assert filesize < 0x20000
                        mo = MeshObject.create_new(filename=new_filename)
                        mo._loaded_from = old_filename
                        meshes.append(mo)

            assert new_gns_filename is not None
            gns = GNSObject.create_new(filename=new_gns_filename)
            gns._template_index = template_index
            gns.read_data()
            assert gns.meshes == meshes
            gns.textures = textures
            gns.gns_pointer = self

            GNSObject.WILDCARD_MAP_OPTIONS.remove(chosen)
            assert chosen not in GNSObject.WILDCARD_MAP_OPTIONS

            EncounterObject.REPLACING_MAPS.append(self.index)
            EncounterObject.REPLACING_MAPS.append(self.index)


class GNSObject(MapMixin):
    flag = 'm'
    flag_description = 'custom maps'

    CUSTOM_MAP_PATH = path.join('custom', 'maps')
    ALTERNATE_MAP_PATH = path.join('custom', 'maps', 'alternate')
    WILDCARD_MAP_PATH = path.join('custom', 'maps', 'wildcard')
    ALTERNATE_MAP_OPTIONS = {}
    WILDCARD_MAP_OPTIONS = []

    filename_matcher = re.compile('^MAP(\d\d\d)\.(GNS|(\d+))')
    for parent, children, filenames in sorted(walk(CUSTOM_MAP_PATH)):
        indexes = set()
        filepaths = set()
        for f in filenames:
            match = filename_matcher.match(f)
            if match:
                indexes.add(match.group(1))
                filepaths.add(path.join(parent, f))
        if filepaths and len(indexes) == 1:
            index = int(list(indexes)[0])
            if parent.startswith(ALTERNATE_MAP_PATH):
                if index not in ALTERNATE_MAP_OPTIONS:
                    ALTERNATE_MAP_OPTIONS[index] = [None]
                ALTERNATE_MAP_OPTIONS[index].append(sorted(filepaths))
            elif parent.startswith(WILDCARD_MAP_PATH):
                WILDCARD_MAP_OPTIONS.append((sorted(filepaths), index))
            else:
                print('WARNING: Uncategorized map in %s' % parent)

    if not (ALTERNATE_MAP_OPTIONS or WILDCARD_MAP_OPTIONS):
        print('WARNING: No custom maps found.')

    WARJILIS = 42
    ZARGHIDAS = 33

    @classproperty
    def after_order(self):
        return [GNSPointerObject]

    @cached_property
    def meshes(self):
        return MeshObject.get_all_by_map_index(self.map_index)

    @cached_property
    def primary_meshes(self):
        return [m for m in self.meshes if m.tiles]

    @cached_property
    def zones(self):
        tiles = self.get_tiles_compare_attribute('no_pass', False)
        done = set()
        zones = []
        while tiles:
            seed = random.choice(tiles)
            zone = {seed}
            while True:
                adjacent = {(x, y) for (x, y) in tiles if
                            (x+1, y) in zone or (x-1, y) in zone or
                            (x, y+1) in zone or (x, y-1) in zone}
                if adjacent <= zone:
                    break
                zone |= adjacent
            zones.append(zone)
            tiles = [t for t in tiles if t not in zone]

        if len(zones) > 1:
            assert (sum(len(z) for z in zones) ==
                        len({t for z in zones for t in z}))
            max_area = max(len(z) for z in zones)
            big_zones = [z for z in zones if len(z) == max_area]
            big_zones = sorted(big_zones, key=lambda z: min(z))
            chosen_zone = random.choice(big_zones)
            for z in zones:
                if z is chosen_zone:
                    continue
                for t in z:
                    self.set_unreachable(*t)

        return zones

    @property
    def width(self):
        widths = {m.width for m in self.primary_meshes}
        return max(widths)

    @property
    def length(self):
        lengths = {m.length for m in self.primary_meshes}
        return max(lengths)

    def read_data(self, filename=None, pointer=None):
        super().read_data(filename, pointer)
        self.zones

    def randomize(self):
        if self.map_index not in self.ALTERNATE_MAP_OPTIONS:
            return

        options = self.ALTERNATE_MAP_OPTIONS[self.map_index]
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
                values = self.get_tile_attribute(x, y, attribute, upper)
                if all(compare_function(v, value) for v in values):
                    coordinates.add((x, y))
        return sorted(coordinates)

    def get_tile_attribute(self, x, y, attribute,
                           upper=False, singleton=False):
        if not hasattr(self, '_tile_cache'):
            self._tile_cache = {}

        key = (x, y, attribute, upper)
        if key in self._tile_cache:
            values = self._tile_cache[key]
            if singleton:
                values = list(values)[0] if len(values) == 1 else values
            return values

        values = {getattr(m.get_tile(x, y, upper=upper), attribute)
                  for m in self.primary_meshes if x < m.width and y < m.length}
        self._tile_cache[key] = values

        return self.get_tile_attribute(x, y, attribute, upper, singleton)

    def set_occupied(self, x, y):
        if not hasattr(self, '_tile_cache'):
            self._tile_cache = {}

        for attribute in ['occupied', 'bad', 'party', 'enemy']:
            for upper in [True, False]:
                key = (x, y, attribute, upper)
                if key in self._tile_cache:
                    del(self._tile_cache[key])

        for m in self.primary_meshes:
            try:
                t = m.get_tile(x, y)
                t.occupied = True
                t = m.get_tile(x, y, upper=True)
                t.occupied = True
            except IndexError:
                pass

    def set_unreachable(self, x, y):
        for m in self.primary_meshes:
            try:
                t = m.get_tile(x, y)
                t.unreachable = True
                t = m.get_tile(x, y, upper=True)
                t.unreachable = True
            except IndexError:
                pass

    def get_occupied(self, x, y):
        for m in self.primary_meshes:
            try:
                t = m.get_tile(x, y)
                if t.occupied:
                    return True
                t = m.get_tile(x, y, upper=True)
                if t.occupied:
                    return True
            except IndexError:
                pass
        return False

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

    def generate_heatmap(self, tiles, max_distance=10):
        heat_values = [100 ** (0.5 ** i) for i in range(max_distance+1)]
        heatmap = [[0] * self.width for _ in range(self.length)]
        heatmap[0][0] = None
        assert heatmap[1][0] is not None
        heatmap[0][0] = 0
        for (x, y) in tiles:
            min_x = max(0, x-max_distance)
            max_x = min(self.width-1, x+max_distance)
            min_y = max(0, y-max_distance)
            max_y = min(self.length-1, y+max_distance)
            for i in range(min_x, max_x+1):
                x_distance = abs(x-i)
                for j in range(min_y, max_y+1):
                    y_distance = abs(y-j)
                    total_distance = x_distance + y_distance
                    if total_distance > max_distance:
                        continue
                    heatmap[j][i] += heat_values[total_distance]
        for j in range(self.length):
            for i in range(self.width):
                heatmap[j][i] = round(heatmap[j][i], 8)
        return heatmap

    def generate_occupied_heatmap(self, attribute='occupied', max_distance=10):
        occupied_tiles = self.get_tiles_compare_attribute(attribute, True)
        return self.generate_heatmap(occupied_tiles, max_distance)

    def get_recommended_tiles(self, attribute='occupied'):
        avg_x = (self.width-1) / 2
        avg_y = (self.length-1) / 2
        heatmap = self.generate_occupied_heatmap(attribute)
        def sortfunc(x_y):
            x, y = x_y
            sig = hashstring('%s%s%s' % (x, y, self.signature))
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
            if DEBUG and (x, y) in enemy_tiles:
                raise Exception('There should not be an enemy here.')
            sig = hashstring('%s%s%s' % (x, y, self.signature))
            partyval = 1 + partymap[y][x]
            enemyval = 1 + enemymap[y][x]
            distances = []
            for ex, ey in enemy_tiles:
                distances.append(abs(x-ex) + abs(y-ey))
            distances = [1/(d**2) for d in distances]
            clumping = (1 + sum(distances))**2
            score = round(enemyval / (partyval * partyval * clumping), 5)
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

    @property
    def pretty_elevation_map(self):
        s = 'Y = %s\n' % (self.length-1)
        for j in range(self.length-1, -1, -1):
            for i in range(self.width):
                value = self.get_tile_attribute(i, j, 'z')
                if len(value) == 1:
                    value = list(value)[0]
                    value = '{0:0>2}'.format(value)
                else:
                    value = '??'
                s += value + ' '
            s = s.strip() + '\n'
        s += 'Y = 0'
        return s.strip()

    @property
    def pretty_depth_map(self):
        s = 'Y = %s\n' % (self.length-1)
        for j in range(self.length-1, -1, -1):
            for i in range(self.width):
                value = self.get_tile_attribute(i, j, 'depth')
                if len(value) == 1:
                    value = list(value)[0]
                    value = '{0:0>2}'.format(value)
                else:
                    value = '??'
                s += value + ' '
            s = s.strip() + '\n'
        s += 'Y = 0'
        return s.strip()

    @property
    def pretty_terrain_map(self):
        s = 'Y = %s\n' % (self.length-1)
        for j in range(self.length-1, -1, -1):
            for i in range(self.width):
                value = self.get_tile_attribute(i, j, 'terrain_type')
                if len(value) == 1:
                    value = list(value)[0]
                    value = '{0:0>2x}'.format(value)
                else:
                    value = '??'
                s += value + ' '
            s = s.strip() + '\n'
        s += 'Y = 0'
        return s.strip()

    def set_new_sectors(self):
        psx_fm = get_psx_file_manager()
        psx_fm.SKIP_REALIGNMENT = True

        new_path = self.filename
        head, new_name = path.split(new_path)
        template = psx_fm.get_file(GNSObject.get(0).filename)
        imported = psx_fm.import_file(new_name, filepath=new_path,
                                      template=template)
        assert self.gns_pointer.is_free
        self.gns_pointer.sector = imported.target_sector

        sector_map = {}
        meshes, textures = [], []
        for obj in self.meshes + self.textures:
            old_path = obj._loaded_from
            template = psx_fm.get_file(old_path)
            old_sector = template.target_sector
            new_path = obj.filename
            with open(old_path, 'rb') as f:
                with open(new_path, 'rb') as g:
                    same_data = f.read() == g.read()

            if same_data:
                remove_unused_file(obj.filename)
                obj._is_removed = True
                sector_map[old_sector] = None
                continue

            head, new_name = path.split(new_path)
            imported = psx_fm.import_file(new_name, filepath=new_path,
                                          template=template)
            sector_map[old_sector] = imported
            if obj in self.meshes:
                meshes.append(imported)
            elif obj in self.textures:
                textures.append(imported)

        f = get_open_file(self.filename)
        num_rows = 0
        while True:
            row_index = num_rows * 20
            f.seek(row_index)
            line = f.read(20)
            if len(line) != 20:
                break
            num_rows += 1

            f.seek(row_index + 4)
            filetype = int.from_bytes(f.read(2), byteorder='little')
            f.seek(row_index + 8)
            sector = int.from_bytes(f.read(4), byteorder='little')
            f.seek(row_index + 12)
            filesize = int.from_bytes(f.read(4), byteorder='little')

            if filetype == 0x3101:
                continue
            if sector not in sector_map:
                continue
            imported = sector_map[sector]
            if imported is None:
                continue

            f.seek(row_index + 8)
            f.write(imported.target_sector.to_bytes(
                length=4, byteorder='little'))

            f.seek(row_index + 12)
            assert not imported.filesize % 0x800
            f.write(imported.filesize.to_bytes(length=4, byteorder='little'))

            if filetype == 0x1701:
                assert imported in textures
            elif filetype in (0x2e01, 0x2f01, 0x3001):
                assert imported in meshes
            else:
                raise Exception('Unknown map file type.')

    def cleanup(self):
        if hasattr(self, '_template_index'):
            assert hasattr(self, 'textures')
            assert hasattr(self, 'gns_pointer')
            self.set_new_sectors()

        if hasattr(self, '_tile_cache'):
            del(self._tile_cache)


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
            if self.occupied:
                return True
            return self.bad_regardless

        @property
        def no_pass(self):
            return self.impassable | self.uncursorable

        @property
        def bad_regardless(self):
            if self.no_pass:
                return True
            if self.slope_height > 2:
                return True
            if self.depth > 2:
                return True
            if self.terrain_type in [0x12, 0x24]:
                # bad terrain : lava, water plant
                return True
            if self.unreachable:
                return True
            return False

        @property
        def enemy(self):
            return self.occupied and not self.party

    @property
    def gns(self):
        gnss = [gns for gns in GNSObject.every
                if gns.map_index == self.map_index]
        if len(gnss) == 1:
            return gnss[0]

    @cached_property
    def terrain_addr(self):
        addr = int.from_bytes(self.data[0x68:0x68+4], byteorder='little')
        # TODO: addr >= 0xb4???
        return addr

    @cached_property
    def width(self):
        return self.data[self.terrain_addr]

    @cached_property
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
        if upper:
            return self.upper[(y * self.width) + x]
        else:
            return self.tiles[(y * self.width) + x]

    def get_tiles_compare_attribute(self, *args, **kwargs):
        return self.gns.get_tiles_compare_attribute(*args, **kwargs)


class TextureObject(MapMixin): pass


class UnitObject(TableObject):
    flag = 'u'
    flag_description = 'enemy and ally units'
    custom_random_enable = flag

    DAYS_IN_MONTH = {1: 31, 2: 28, 3: 31, 4: 30, 5: 31, 6: 30,
                     7: 31, 8: 31, 9: 30, 10: 31, 11: 30, 12: 31}

    MONSTER_GRAPHIC = 0x82
    MALE_GRAPHIC = 0x80
    FEMALE_GRAPHIC = 0x81
    GENERIC_GRAPHICS = (MALE_GRAPHIC, FEMALE_GRAPHIC)
    CHOCOBO_SPRITE_ID = (0x82, 0x86)
    NO_JOB_CHANGE = {0x91}

    EQUIPMENT_ATTRS = ['head', 'body', 'accessory', 'righthand', 'lefthand']

    INITIAL_STAT_VALUES = {
        'male':    {'hp':  (0x78000, 0x7ffff),
                    'mp':  (0x38000, 0x3bfff),
                    'spd': (0x18000, 0x18000),
                    'pa':  (0x14000, 0x14000),
                    'ma':  (0x10000, 0x10000),
                   },
        'female':  {'hp':  (0x70000, 0x77fff),
                    'mp':  (0x3c000, 0x3ffff),
                    'spd': (0x18000, 0x18000),
                    'pa':  (0x10000, 0x10000),
                    'ma':  (0x14000, 0x14000),
                   },
        'monster': {'hp':  (0x8c000, 0x97fff),
                    'mp':  (0x18000, 0x23fff),
                    'spd': (0x14000, 0x14000),
                    'pa':  (0x14000, 0x17fff),
                    'ma':  (0x14000, 0x17fff),
                   },
        }

    @classproperty
    def CHANGED_RAMZA_ENTD_INDEXES(self):
        if get_global_label() == 'FFT_TLW':
            return {0x100, 0x181, 0x101, 0x102}
        else:
            return {0x100, 0x133, 0x183, 0x188}

    @classproperty
    def after_order(self):
        return [GNSObject, ENTDObject, SkillsetObject, JobReqObject, JobObject]

    @cached_property
    def entd_index(self):
        return self.index >> 4

    @cached_property
    def entd(self):
        return ENTDObject.get(self.entd_index)

    @cached_property
    def is_valid(self):
        if not (self.is_present or self.is_important):
            return False
        if not self.entd.is_valid:
            return False
        return True

    @cached_property
    def rank(self):
        if self.entd.avg_level is not None:
            rank = self.entd.avg_level
            if self.old_job.is_lucavi:
                rank *= 1.5
            return rank
        return -1

    @clached_property
    def human_unit_pool(self):
        return [u for u in self.ranked if (u.is_present or u.is_important)
                and u.entd.is_valid and u.rank >= 0 and u.is_human_old]

    @property
    def is_dead(self):
        return self.old_job.is_dead

    @property
    def is_human(self):
        return (self.graphic != self.MONSTER_GRAPHIC
                and not (self.job.is_monster or self.job.is_lucavi))

    @cached_property
    def is_human_old(self):
        return (self.old_data['graphic'] != self.MONSTER_GRAPHIC
                and not self.old_job.is_lucavi)

    @property
    def is_chocobo(self):
        return self.sprite_id == self.CHOCOBO_SPRITE_ID

    @property
    def human_unit_pool_member(self):
        if hasattr(self, '_human_unit_pool_member'):
            return self._human_unit_pool_member

        for u in UnitObject.every:
            u._human_unit_pool_member = None

        for u in self.human_unit_pool:
            u._human_unit_pool_member = u

        for e in ENTDObject.every:
            units = e.units
            pool_units = [u for u in units if u._human_unit_pool_member]
            if 1 <= len(pool_units) <= len(units):
                member = sorted(pool_units, key=lambda u: u.signature)[0]
                for u in units:
                    if u._human_unit_pool_member is None:
                        u._human_unit_pool_member = member

        return self.human_unit_pool_member

    @clached_property
    def special_unit_pool(self):
        pool = [u for u in self.ranked if u.is_valid and u.rank >= 0
                and not (u.old_job.is_generic or u.old_job.is_monster)
                and u.old_job.old_data['skillset_index'] > 0
                and u.get_gender() is not None
                and u.character_name != 'Ramza']
        pool = [u for u in pool if u.old_job.character_name == 'NONE'
                or 1 <= u.old_data['name_index'] <= 0xfd]
        if self.random_difficulty > 1.0:
            pool = [u for u in pool if not u.is_dead]
        balmafula = [u for u in self.ranked if u.character_name == 'Balmafula'
                     and u.get_gender() == 'female']
        balmafula = random.choice(balmafula)
        max_index = len(pool) - 1
        index = max_index // 2
        pool.insert(index, balmafula)
        return pool

    @clached_property
    def monster_pool(self):
        return [u for u in self.ranked if u.is_valid
                and u.old_job.is_generic and u.old_job.is_monster]

    @clached_property
    def brave_faith_unit_pool(self):
        return self.human_unit_pool + self.special_unit_pool

    @clached_property
    def fixed_brave_faith_pool(self):
        pool = [u for u in self.brave_faith_unit_pool
                if all(1 <= u.old_data[attr] <= 0xfd
                       for attr in ('brave', 'faith'))]
        return sorted({(u.old_data['brave'], u.old_data['faith'])
                       for u in pool})

    @clached_property
    def chocobo_pool(self):
        return [u for u in self.ranked if u.is_valid
                and u.old_sprite_id == self.CHOCOBO_SPRITE_ID]

    @clached_property
    def all_used_skillsets(self):
        max_index = len(SkillsetObject.every)-1
        pool = {u.old_data['secondary'] for u in UnitObject.every
                if u.is_valid}
        pool |= {u.old_job.old_data['skillset_index'] for u in UnitObject.every
                 if u.is_valid}
        pool = [SkillsetObject.get(i) for i in sorted(pool)
                if 5 <= i <= max_index]
        pool = [p for p in pool if set(p.old_action_indexes) != {0}]
        return pool

    @property
    def requires_sword(self):
        if SkillsetObject.get(self.job.skillset_index).requires_sword:
            return True
        if (1 <= self.secondary <= 0xfd and
                SkillsetObject.get(self.secondary).requires_sword):
            return True
        return False

    @property
    def two_swords(self):
        for i in self.job.innates:
            if i == AbilityObject.TWO_SWORDS:
                return True
        if self.support == AbilityObject.TWO_SWORDS:
            return True
        return False

    @property
    def neighbors(self):
        return self.entd.units

    @property
    def character_name(self):
        name_index = self.old_data['name_index']
        name = names.characters[name_index]
        if not name.strip():
            return '{0:0>2X}-NO-NAME'.format(name_index)
        return name

    @property
    def has_unique_name(self):
        if 'NO-NAME' in self.character_name:
            return False
        if self.character_name == 'RANDOM GENERIC':
            return False
        return bool(self.character_name.strip())

    @property
    def has_unique_name_index(self):
        return 1 <= self.name_index <= 0xfe

    @clached_property
    def canonical_named_units(self):
        canon = {}
        for u in UnitObject.every:
            if u.has_unique_name:
                name = u.character_name
                if name not in canon or not canon[name].entd.is_valid:
                    canon[u.character_name] = u
        return canon

    @property
    def canonical_relative(self):
        if not self.has_unique_name_index:
            return self
        if not names.characters[self.name_index]:
            return self
        return self.canonical_named_units[names.characters[self.name_index]]

    @property
    def is_canonical(self):
        return self.canonical_relative is self

    @property
    def has_generic_sprite(self):
        if self.graphic == self.MONSTER_GRAPHIC:
            return JobObject.get(self.job_index).is_monster
        if self.graphic in self.GENERIC_GRAPHICS:
            return JobObject.get(self.job_index).is_generic
        return False

    @property
    def has_generic_sprite_old(self):
        if self.old_data['graphic'] == self.MONSTER_GRAPHIC:
            return JobObject.get(self.old_data['job_index']).is_monster
        if self.old_data['graphic'] in self.GENERIC_GRAPHICS:
            return JobObject.get(self.old_data['job_index']).is_generic
        return False

    @property
    def sprite_id(self):
        if self.graphic == self.MONSTER_GRAPHIC:
            job_sprite = self.job.monster_portrait
        elif self.graphic in self.GENERIC_GRAPHICS:
            job_sprite = self.job_index
        else:
            job_sprite = None
        return self.graphic, job_sprite

    @property
    def old_sprite_id(self):
        if self.old_data['graphic'] == self.MONSTER_GRAPHIC:
            job_sprite = self.old_job.old_data['monster_portrait']
            if job_sprite == 0:
                job_sprite = self.old_data['job_index']
        elif self.old_data['graphic'] in self.GENERIC_GRAPHICS:
            job_sprite = self.old_data['job_index']
        else:
            job_sprite = None
        return self.old_data['graphic'], job_sprite

    def set_sprite(self, sprite_id):
        graphic, job_sprite = sprite_id
        if graphic == self.MONSTER_GRAPHIC:
            candidates = [j for j in JobObject.every
                          if j.monster_portrait == job_sprite]
            self.job_index = random.choice(candidates).index
        elif graphic in self.GENERIC_GRAPHICS:
            self.job_index = job_sprite
        self.graphic = graphic
        assert sprite_id == self.sprite_id

    def get_similar_sprite(self, exclude_sprites=None, random_degree=None):
        if exclude_sprites is None:
            exclude_sprites = set()
        if random_degree is None:
            random_degree = UnitObject.random_degree
        exclude_sprites = {
            (self.MALE_GRAPHIC if g == self.FEMALE_GRAPHIC else g, j)
            for (g, j) in exclude_sprites}
        graphic, job_sprite = self.old_sprite_id
        if graphic == UnitObject.MONSTER_GRAPHIC:
            candidates = [
                j for j in JobObject.ranked_monsters
                if (graphic, j.monster_portrait) not in exclude_sprites]
            new_monster = self.old_job.get_similar(
                candidates=candidates, override_outsider=True, wide=True,
                random_degree=random_degree, presorted=True)
            new_sprite = graphic, new_monster.monster_portrait
            assert new_sprite not in exclude_sprites
            return new_sprite

        elif graphic in UnitObject.GENERIC_GRAPHICS:
            jro_jps = {jro.job_index: jro.get_jp_total()
                       for jro in JobReqObject.every}
            max_jp = max(jro_jps.values())

            if job_sprite == JobObject.SQUIRE_INDEX:
                jp = 0
            else:
                jro = JobReqObject.get_by_job_index(job_sprite)
                jp = jro.get_jp_total(old=True)
                if (self.get_bit('enemy_team')
                        and self.entd_index not in ENTDObject.NERF_ENTDS):
                    jp = (jp * self.random_difficulty
                          * JobReqObject.jp_increase_ratio)
                else:
                    jp /= 2
                jp = mutate_normal(jp, 0, max(jp, max_jp),
                                   random_degree=random_degree)
                jp = round(jp * 2, -2) // 2
            candidates = sorted(
                jro_jps, key=lambda jro_index: (
                    jro_jps[jro_index],
                    JobReqObject.get_by_job_index(jro_index).signature))
            candidates = [
                c for c in candidates
                if (self.MALE_GRAPHIC, c) not in exclude_sprites]
            temp = [c for c in candidates if jro_jps[c] >= jp]
            if temp:
                max_index = len(temp) - 1
                factor = random.random() ** (1 / self.random_degree ** 2)
                index = int(round(factor * max_index))
                chosen = temp[0]
            else:
                chosen = random.choice(candidates)
            index = candidates.index(chosen)
            squire = (UnitObject.MALE_GRAPHIC, JobObject.SQUIRE_INDEX)
            if (index == 0 and squire not in exclude_sprites
                    and random.choice([True, False])):
                chosen = JobObject.SQUIRE_INDEX
            else:
                max_index = len(candidates)-1
                index = mutate_normal(
                    index, 0, max_index,
                    random_degree=random_degree)
                chosen = candidates[index]
            assert JobObject.SQUIRE_INDEX <= chosen <= JobObject.MIME_INDEX
            gender = random.choice(UnitObject.GENERIC_GRAPHICS)
            return gender, chosen

    def get_special_sprite(self):
        if self.rank >= 0:
            unit = self
        else:
            max_index = len(self.special_unit_pool) - 1
            index = int(round(self.job.ranked_ratio * max_index))
            unit = self.special_unit_pool[index]

        chosen = unit.get_similar(
            candidates=self.special_unit_pool, override_outsider=True,
            wide=True, presorted=True,
            random_degree=UnitObject.random_degree ** 1.5)
        assert chosen in self.special_unit_pool
        return chosen

    @property
    def job(self):
        return JobObject.get(self.job_index)

    @property
    def old_job(self):
        return JobObject.get(self.old_data['job_index'])

    @property
    def is_monster(self):
        return self.job.is_monster

    @property
    def is_ally(self):
        return not (
            self.get_bit('enemy_team') or self.get_bit('alternate_team'))

    @property
    def presence(self):
        return (self.get_bit('randomly_present'),
                self.get_bit('always_present'), self.unit_id)

    @cached_property
    def presence_old(self):
        return (self.get_bit('randomly_present', old=True),
                self.get_bit('always_present', old=True),
                self.old_data['unit_id'])

    @cached_property
    def is_present(self):
        return (
            self.get_bit('randomly_present') or self.get_bit('always_present')
            or self.unit_id != 0xff)

    @cached_property
    def is_present_old(self):
        return (
            self.get_bit('randomly_present', old=True)
            or self.get_bit('always_present', old=True)
            or self.old_data['unit_id'] != 0xff)

    @cached_property
    def is_important(self):
        if self.has_unique_name:
            return True
        return self.entd.is_valid and self.is_present and self.unit_id != 0xff

    @cached_property
    def is_important_map_movements(self):
        return (self.get_bit('randomly_present')
                or self.get_bit('always_present') or 1 <= self.unit_id <= 0x7f)

    @cached_property
    def encounter(self):
        if self.entd_index == 0:
            return None

        for e in EncounterObject.every:
            if e.entd_index == self.entd_index:
                return e.canonical_relative

    @property
    def map(self):
        if self.encounter:
            return self.encounter.map

    @property
    def old_map(self):
        indexes = {e.old_data['map_index'] for e in EncounterObject.every
                   if e.old_data['entd_index'] == self.entd_index}
        if len(indexes) == 1:
            return GNSObject.get(list(indexes)[0])

    def calculate_stat_value(self, attr, level=None):
        if level is None:
            level = self.level
        if not 1 <= level <= 99:
            return

        gender = self.get_gender()
        if gender is None:
            return

        low, high = self.INITIAL_STAT_VALUES[gender][attr]
        growth_value = getattr(self.job, '%sgrowth' % attr)
        for i in range(1, level):
            low += low / (growth_value + i)
            high += high / (growth_value + i)

        mult_value = getattr(self.job, '%smult' % attr)
        low = low * mult_value / 1638400
        high = high * mult_value / 1638400

        return int(low), int(high)

    def normalize_level(self, boost=None):
        if not boost:
            self.level = 0xfe
        else:
            self.level = 100 + boost
            self.level = max(100, min(self.level, 199))

    @property
    def facing(self):
        return self.misc_facing & 0x3

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
        self.misc_facing &= 0xFC
        self.misc_facing |= chosen

    @property
    def is_upper(self):
        return bool(self.misc_facing & 0x80)

    @property
    def is_upper_old(self):
        return bool(self.old_data['misc_facing'] & 0x80)

    def set_upper(self, upper):
        if upper:
            self.misc_facing |= 0x80
        else:
            self.misc_facing &= 0x7f

    def relocate(self, x, y):
        assert not self.map.get_occupied(x, y)
        if (hasattr(self, '_fixed_initial_coordinates') and
                self._fixed_initial_coordinates and
                not hasattr(self.map, '_loaded_from')):
            raise IndexError('Unit must retain initial coordinates.')
        if self.is_ally:
            self.map.set_party(x, y)
        else:
            self.map.set_occupied(x, y)
        self.x = x
        self.y = y
        self.set_upper(False)
        if not self.map.get_tile_attribute(self.x, self.y, 'bad_regardless',
                                           upper=True, singleton=True):
            if random.choice([True, True, False]):
                self.set_upper(True)

    def find_appropriate_position(self):
        random_degree = EncounterObject.random_degree

        if self.is_ally:
            tiles = self.map.get_recommended_tiles_ally()
        else:
            tiles = self.map.get_recommended_tiles_enemy()

            compare_function = lambda a, b: a >= b
            depth_tiles = self.map.get_tiles_compare_attribute(
                'depth', 1, upper=False,
                compare_function=compare_function)

            tiles = [t for t in tiles if t not in depth_tiles]

        max_index = len(tiles)-1
        factor = 1 - (random.random() ** (1 / (random_degree ** 0.7)))
        assert 0 <= factor <= 1
        index = int(round(max_index * factor))
        x, y = tiles[index]

        self.relocate(x, y)
        self.fix_facing()

    def relocate_nearest_good_tile(self, max_distance=16, upper=None,
                                   preserve_elevation=None):
        if upper is None:
            upper = self.is_upper
        neighbor_coordinates = [(u.x, u.y) for u in self.neighbors
                                if u.is_present]
        valid_tiles = self.map.get_tiles_compare_attribute('bad', False)

        if isinstance(preserve_elevation, int):
            compare_function = lambda a, b: a >= b
            depth_tiles = self.map.get_tiles_compare_attribute(
                'depth', 1, upper=upper,
                compare_function=compare_function)
            z = preserve_elevation
            best_height_tiles = self.map.get_tiles_compare_attribute(
                'z', z, upper=upper)
            compare_function = lambda a, b: abs(a-b) <= 2
            valid_height_tiles = self.map.get_tiles_compare_attribute(
                'z', z, upper=upper, compare_function=compare_function)
            valid_tiles = [t for t in valid_tiles
                           if t in valid_height_tiles
                           and t not in depth_tiles]

        for distance in range(max_distance+1):
            candidates = [(x, y) for (x, y) in valid_tiles
                          if abs(x-self.x) + abs(y-self.y) <= distance
                          and (x, y) not in neighbor_coordinates]
            if isinstance(preserve_elevation, int):
                temp = [c for c in candidates if c in best_height_tiles]
                if temp:
                    candidates = temp
            if candidates:
                x, y = random.choice(candidates)
                self.relocate(x, y)
                return (x, y)
        else:
            raise IndexError('No good tiles.')

    def preprocess(self):
        if self.index == 0x153d and not self.is_important:
            self.set_bit('always_present', False)
            self.old_data['misc2'] = self.misc2

    def clear_gender(self):
        self.set_bit('female', False)
        self.set_bit('male', False)
        self.set_bit('monster', False)

    def get_gender(self):
        genders = [gender for gender in ['male', 'female', 'monster']
                   if self.get_bit(gender)]
        if len(genders) == 1:
            return genders[0]

    def become_another(self, other):
        if self is other:
            return
        for attr in ['graphic', 'name_index', 'month', 'day',
                     'brave', 'faith', 'unlocked', 'unlocked_level',
                     'job_index', 'palette']:
            setattr(self, attr, other.old_data[attr])
        for attr in UnitObject.EQUIPMENT_ATTRS + [
                 'secondary', 'reaction', 'support', 'movement']:
            if random.choice([True, False]):
                setattr(self, attr, other.old_data[attr])
        self.set_bit('always_present', True)
        self.clear_gender()
        self.set_bit(other.get_gender(), True)
        self.clear_cache()
        self._copied_from = other

    def reset_blank(self):
        self.name_index = 0xff
        self.unit_id = 0xff
        self.unknown2 = 0xfffe
        for attr in ['level', 'unlocked', 'unlocked_level', 'job_index',
                     'trophy', 'gil', 'unknown3', 'unknown4', 'behavior',
                     'target_id', 'misc1', 'misc2', 'graphic', 'palette']:
            setattr(self, attr, 0)
        for attr in (['month', 'day', 'brave', 'faith', 'secondary']
                + UnitObject.EQUIPMENT_ATTRS):
            setattr(self, attr, 0xfe)
        for attr in ['reaction', 'support', 'movement']:
            setattr(self, attr, 0x1fe)

    def randomize_job(self):
        if self.old_job.index in self.NO_JOB_CHANGE:
            assert self.job == self.old_job
            return

        if hasattr(self, '_target_sprite'):
            if isinstance(self._target_sprite, UnitObject):
                self.become_another(self._target_sprite)
            else:
                graphic, job_index, gender = self._target_sprite
                self.graphic = graphic
                self.job_index = job_index
                if gender is not None:
                    self.clear_gender()
                    self.set_bit(gender, True)
            return

        if not self.has_generic_sprite:
            if self.job.is_generic and self.graphic > 0:
                # pretty much just Algus
                candidates = [u for u in UnitObject.every if u.entd.is_valid
                              and u.is_present]
                chosen = random.choice(candidates)
                self.job_index = chosen.old_data['job_index']
            return

        neighbors = [u for u in self.neighbors
                     if u.is_present_old and u.has_generic_sprite_old]

        available_sprites = self.entd.available_sprites
        if (self.old_sprite_id == self.CHOCOBO_SPRITE_ID
                and self.unit_id != 0xff):
            available_sprites = [s for s in available_sprites
                                 if not isinstance(s, UnitObject)]
            available_sprites = [(g, j) for (g, j) in available_sprites
                                 if g == self.MONSTER_GRAPHIC]

        for _ in range(10):
            if available_sprites:
                test = random.choice(available_sprites)
            else:
                available_sprites = [u._target_sprite for u in self.neighbors
                                     if hasattr(u, '_target_sprite')]
                assert all(len(s) == 3 for s in available_sprites
                           if not isinstance(s, UnitObject))
                temp = []
                for a in available_sprites:
                    if isinstance(a, UnitObject):
                        temp.append(a)
                        continue

                    g, j, gender = a
                    if gender == 'monster':
                        assert g == self.MONSTER_GRAPHIC
                        j = JobObject.get(j).monster_portrait
                        assert j >= SpriteMetaObject.CHOCOBO_INDEX
                    else:
                        assert g in (self.MALE_GRAPHIC, self.FEMALE_GRAPHIC)
                    temp.append((g, j))
                available_sprites = temp
                test = random.choice(available_sprites)

            if (isinstance(test, UnitObject)
                    and random.random() > self.random_degree ** 0.5):
                continue
            break

        assert all(len(s) == 2 for s in available_sprites
                   if not isinstance(s, UnitObject))

        if isinstance(test, UnitObject):
            self.become_another(test)
            return

        available_sprites = [s for s in available_sprites
                             if not isinstance(s, UnitObject)]
        for _ in range(0x10):
            template = random.choice(neighbors)
            template_job = template.old_job
            tg, tj = template.old_sprite_id
            candidates = [
                (g, j) for (g, j) in available_sprites
                if ((g == self.MONSTER_GRAPHIC) ==
                    (tg == self.MONSTER_GRAPHIC))]
            if candidates:
                break
        else:
            tg, tj = random.choice(available_sprites)
            candidates = available_sprites
            template_job = [j for j in JobObject.every if j.sprite_id == tj][0]

        if tg != self.MONSTER_GRAPHIC:
            self.graphic, self.job_index = random.choice(candidates)
            self.clear_gender()
            if self.graphic == self.MALE_GRAPHIC:
                self.set_bit('male', True)
            elif self.graphic == self.FEMALE_GRAPHIC:
                self.set_bit('female', True)
            else:
                raise Exception('Sprite leak.')
        elif tg == self.MONSTER_GRAPHIC:
            mgraphics = [j for (g, j) in available_sprites
                         if g == self.MONSTER_GRAPHIC]
            assert all(j >= SpriteMetaObject.CHOCOBO_INDEX for j in mgraphics)
            candidates = [j for j in JobObject.every
                          if j.is_monster and j.monster_portrait in mgraphics
                          and j.intershuffle_valid]
            similar = template_job.get_similar(
                candidates=candidates, random_degree=self.random_degree,
                override_outsider=True, wide=True)
            self.graphic = self.MONSTER_GRAPHIC
            self.job_index = similar.index
            self.clear_gender()
            self.set_bit('monster', True)

    def randomize_equips(self):
        if self.job.is_monster:
            for equip in UnitObject.EQUIPMENT_ATTRS:
                setattr(self, equip, 0)
            return

        for equip in UnitObject.EQUIPMENT_ATTRS:
            if self.rank < 0:
                template = self
            else:
                unit = self.human_unit_pool_member

                if unit:
                    template = unit.get_similar(
                        candidates=self.human_unit_pool, presorted=True)
                else:
                    template = self

            tequips = [template.old_data[q] for q in UnitObject.EQUIPMENT_ATTRS
                       if 1 <= template.old_data[q] <= 0xfd]
            if not tequips:
                tequips = [self.old_data[q] for q in UnitObject.EQUIPMENT_ATTRS
                           if 1 <= self.old_data[q] <= 0xfd]
            if not tequips:
                continue
            if len(tequips) < 5:
                test = random.choice(tequips + [None])
                if test is None:
                    continue

            if equip in ['righthand', 'lefthand']:
                candidates = ItemObject.ranked_hands_candidates
            else:
                candidates = ItemObject.ranked_nohands_candidates

            if random.random() > self.random_degree ** 3:
                if (equip == 'righthand'
                        or (equip == 'lefthand' and self.two_swords)):
                    candidates = [c for c in candidates if c.get_bit('weapon')]
                elif equip == 'lefthand':
                    candidates = [c for c in candidates if c.get_bit('shield')]
                else:
                    candidates = [c for c in candidates if c.get_bit(equip)]

            if random.random() > self.random_degree ** 2:
                candidates = [c for c in candidates if self.job.can_equip(c)]

            if equip == 'righthand' and self.requires_sword:
                swords = [c for c in candidates if c.is_sword]
                if swords and random.random() > self.random_degree:
                    candidates = swords
                elif (len(swords) == 0
                        and random.random() < self.random_degree ** 0.5):
                    candidates = [
                        c for c in ItemObject.ranked_hands_candidates
                        if c.is_sword]

            if not candidates:
                setattr(self, equip, 0xfe)
                continue

            tequip = ItemObject.get(random.choice(tequips))
            if self.has_unique_name and 1 <= self.old_data[equip] <= 0xfd:
                old_equip = ItemObject.get(self.old_data[equip])
                if old_equip.rank > tequip.rank:
                    tequip = old_equip

            new_equip = tequip.get_similar(
                candidates=candidates, random_degree=self.random_degree,
                override_outsider=True, wide=True, presorted=True)

            setattr(self, equip, new_equip.index)

    def randomize_handedness(self):
        if random.random() < self.random_degree / 2:
            self.lefthand, self.righthand = self.righthand, self.lefthand

    def randomize_lucavi_secondary(self):
        difficulty = self.random_difficulty

        if self.job.is_lucavi:
            if self.job.index == JobObject.ALTIMA_PERFECT_BODY:
                old = False
            else:
                old = True
            self.job.skillset.absorb_skills(
                SkillsetObject.get(self.job.skillset.index + 1), old=old)
            if not self.job.is_altima:
                valid = {s for s in SkillsetObject.every
                         if s.is_lucavi_appropriate}
                pool = [s for s in self.all_used_skillsets
                        if s in valid]
                self.secondary = random.choice(pool).index
                assert 1 <= self.secondary <= 0xfd

        if (self.job.index == JobObject.ALTIMA_PERFECT_BODY
                and difficulty >= 1):
            candidates = [j for j in JobReqObject.every
                          if j.calculator_potential > 0]
            candidates = sorted(
                candidates,
                key=lambda j: (j.calculator_potential, j.signature))
            max_index = len(candidates)-1
            if difficulty == 1:
                index = random.randint(0, max_index)
            else:
                index = max_index
            self.unlocked = (candidates[index].job_index
                             - JobObject.SQUIRE_INDEX)

            max_level = 8
            ratio = difficulty / (difficulty + 1)
            ratio = mutate_normal(ratio, 0, 1, wide=True, return_float=True,
                                  random_degree=self.random_degree)
            level = int(round(ratio * max_level))

            self.unlocked_level = level
            self.secondary = SkillsetObject.MATH
            return

        if self.job.index == JobObject.ALTIMA_NICE_BODY:
            self.unlocked, self.unlocked_level = 0, 0
            self.secondary = SkillsetObject.CHAOS

    def randomize_secondary(self):
        if self.job.is_monster:
            return

        if self.job.is_lucavi:
            return self.randomize_lucavi_secondary()

        difficulty = self.random_difficulty
        generic_jobs = JobObject.ranked_generic_jobs_candidates

        if (self.job.is_generic
                and not self.job.index == JobObject.SQUIRE_INDEX):
            jp_jobs = [
                j for j in generic_jobs if
                self.job.jobreq.reqs_are_subset_of(j.jobreq)]
        else:
            jp_jobs = generic_jobs

        jp_jobs = sorted(jp_jobs,
                         key=lambda j: (j.get_jp_total(), j.signature))

        if self.job.jobreq and self.job.jobreq.squire_only:
            jp_jobs = [JobObject.get_by_name('squire')] + jp_jobs

        if self.ranked_ratio is not None:
            max_index = len(jp_jobs) - 1
            index = int(round(mutate_normal(
                self.ranked_ratio, 0, 1, random_degree=self.random_degree,
                return_float=True, wide=True) * max_index))
            jp_job = jp_jobs[index]

            jp_job_level = int(round(mutate_normal(
                self.ranked_ratio, 0, 1, random_degree=self.random_degree,
                return_float=True, wide=True) * 8))
        else:
            jp_job = random.choice(jp_jobs)
            jp_job_level = random.randint(0, 8)

        if jp_job.index == JobObject.SQUIRE_INDEX and self.job.jobreq:
            jp_job_level = max(jp_job_level, self.job.jobreq.get_req('squ'))

        self.unlocked = jp_job.index - JobObject.SQUIRE_INDEX
        self.unlocked_level = jp_job_level

        skillset_jobs = set()
        if self.job.jobreq:
            skillset_jobs |= {
                j for j in generic_jobs if
                j.jobreq.reqs_are_subset_of(self.job.jobreq)}
        if jp_job.jobreq:
            skillset_jobs |= {
                j for j in generic_jobs if
                j.jobreq.reqs_are_subset_of(jp_job.jobreq)}

        if self.job.is_generic:
            skillset_jobs.add(JobObject.get(JobObject.SQUIRE_INDEX))

        skillset_jobs = sorted(
            skillset_jobs, key=lambda j: (j.get_jp_total(),
                                          j.signature))

        if self.human_unit_pool_member:
            template = self.human_unit_pool_member.get_similar(
                candidates=self.human_unit_pool, presorted=True)
        else:
            template = random.choice(self.human_unit_pool)

        rsm_attrs = ['reaction', 'support', 'movement']
        if (any(1 <= template.old_data[attr] <= 0x1fd for attr in rsm_attrs)
                or 1 <= template.old_data['secondary'] <= 0xfd):
            if random.random() < self.random_degree ** 2:
                chosen = random.choice(UnitObject.all_used_skillsets)
                self.secondary = chosen.index
            else:
                if self.ranked_ratio is not None:
                    max_index = len(skillset_jobs) - 1
                    index = int(round(mutate_normal(
                        self.ranked_ratio, 0, 1,
                        random_degree=self.random_degree,
                        return_float=True, wide=True) * max_index))
                    chosen = skillset_jobs[index]
                else:
                    chosen = random.choice(skillset_jobs)
                self.secondary = chosen.skillset_index

        for attr in rsm_attrs:
            if self.human_unit_pool_member:
                template = self.human_unit_pool_member.get_similar(
                    candidates=self.human_unit_pool, presorted=True)
            else:
                template = random.choice(self.human_unit_pool)

            if not any(1 <= template.old_data[attr2] <= 0x1fd
                       for attr2 in rsm_attrs):
                continue

            if random.random() < self.random_degree:
                if random.random() < self.random_degree ** 2:
                    pool = getattr(AbilityObject, '%s_pool' % attr)
                else:
                    pool = {rsm for job in skillset_jobs
                            for rsm in job.rsms
                            if getattr(rsm , 'is_%s' % attr)}
            else:
                pool = {rsm for rsm in self.job.rsms
                        if getattr(rsm, 'is_%s' % attr)}

            if not pool:
                continue

            if isinstance(pool, set):
                pool = sorted(pool, key=lambda rsm: (rsm.rank, rsm.signature))

            if self.ranked_ratio is not None:
                max_index = len(pool) - 1
                index = int(round(mutate_normal(
                    self.ranked_ratio, 0, 1, random_degree=self.random_degree,
                    return_float=True, wide=True) * max_index))
                chosen = pool[index]
            else:
                chosen = random.choice(pool)

            setattr(self, attr, chosen.index)

    @property
    def allegiance(self):
        return (self.get_bit('enemy_team') |
                (self.get_bit('alternate_team') << 1))

    def randomize_allegiance(self):
        if self.human_unit_pool_member:
            other = self.human_unit_pool_member.get_similar(
                candidates=self.human_unit_pool, wide=True, presorted=True,
                random_degree=EncounterObject.random_degree)
        else:
            other = random.choice(self.human_unit_pool)
        if other.get_bit('enemy_team'):
            self.set_bit('enemy_team', True)
            self.set_bit('alternate_team', False)
        else:
            if (random.random() < self.random_degree ** 0.5
                    and random.choice([True, False])):
                self.set_bit('enemy_team', True)
                self.set_bit('alternate_team', True)
            else:
                self.set_bit('enemy_team', False)
                self.set_bit('alternate_team', False)
                self.set_bit('join_after_event', True)

    def fix_palette(self):
        if self.graphic == self.MONSTER_GRAPHIC or not self.has_generic_sprite:
            return
        enemy_palettes = [
            u.old_data['palette'] for u in self.neighbors if u.is_present_old
            and u.has_generic_sprite and u.get_bit('enemy_team') and
            u.old_data['graphic'] != self.MONSTER_GRAPHIC]
        if self.get_bit('alternate_team'):
            options = sorted(set(range(1, 4)) - set(enemy_palettes))
            if not options:
                options = lange(1, 4)
            self.palette = random.choice(options)
        elif self.get_bit('enemy_team'):
            if enemy_palettes:
                c = Counter(enemy_palettes)
                most = max(c.values())
                options = [key for key in sorted(c) if c[key] == most]
                self.palette = random.choice(options)
            else:
                self.palette = 3
        else:
            self.palette = 0

    def randomize_brave_faith_zodiac(self):
        if self.has_unique_name_index and not self.is_canonical:
            return

        randomize_birthday = False
        if not self.has_unique_name:
            candidates = self.brave_faith_unit_pool
            bday = random.choice(candidates)
            if 1 <= bday.month <= 13:
                randomize_birthday = True
            self.brave = random.choice(candidates).old_data['brave']
            self.faith = random.choice(candidates).old_data['faith']
        else:
            candidates = self.fixed_brave_faith_pool
            brave, faith = random.choice(candidates)
            self.brave = brave
            brave, faith = random.choice(candidates)
            self.faith = faith
            randomize_birthday = True

        if randomize_birthday:
            self.month = random.randint(0, 12)
            if self.month in self.DAYS_IN_MONTH:
                self.day = random.randint(1, self.DAYS_IN_MONTH[self.month])
            else:
                self.day = 0

        for attr in ['brave', 'faith']:
            value = getattr(self, attr)
            if 0 <= value <= 100:
                value = mutate_normal(value, 0, 100,
                                      random_degree=self.random_degree)
                setattr(self, attr, value)

    def randomize(self):
        if not self.is_present:
            return

        self.randomize_brave_faith_zodiac()
        self.randomize_job()
        if not self.get_bit('load_formation'):
            self.randomize_secondary()
            self.randomize_equips()
            self.randomize_handedness()
        super().randomize()

    def mutate(self):
        if 1 <= self.level <= 99:
            level = mutate_normal(self.level, 1, 99, return_float=True,
                                  random_degree=self.random_degree**1.5)
            if self.get_bit('enemy_team'):
                boost = level * (self.random_difficulty ** 0.5)
                ratio = sum([random.random() for _ in range(3)]) / 3
                level = (level * ratio) + (boost * (1-ratio))
            self.level = max(1, min(99, int(round(level))))

    @property
    def is_standing_on_solid_ground(self):
        if self.map.get_tile_attribute(self.x, self.y, 'depth') != {0}:
            return False
        start_status = self.job.innate_status | self.job.start_status
        if start_status & JobObject.FLOAT_STATUS:
            return False
        return True

    @cached_property
    def full_movement_path(self):
        movement_path = []

        if self.get_bit('always_present') or self.get_bit('randomly_present'):
            start = (self.x, self.y)
            movement_path.append(start)

        if self.encounter is not None:
            movements = self.encounter.get_movements()
            if movements and self.unit_id in movements[0]:
                movement_path += movements[0][self.unit_id]

        return movement_path

    def attempt_chocobo_knight(self):
        if hasattr(self, '_chocobo_rider'):
            return

        candidates = [u for u in self.neighbors if u.is_human
                      #and u.unit_id >= 0x80
                      and (1 <= u.unit_id < 0xff or u.is_present)
                      and u.is_standing_on_solid_ground
                      and not hasattr(u, '_chocobo_mount')]
        temp = [c for c in candidates if c.allegiance == self.allegiance]
        if temp:
            candidates = temp
        old_x, old_y = self.x, self.y
        random.shuffle(candidates)
        for chosen in candidates:
            movement_path = chosen.full_movement_path
            if not movement_path:
                continue
            chosen_x, chosen_y = movement_path[-1]
            self.x = chosen_x
            self.y = chosen_y
            z = self.map.get_tile_attribute(chosen_x, chosen_y, 'z',
                                            upper=chosen.is_upper)
            if len(z) != 1:
                continue
            z = list(z)[0]
            try:
                self.relocate_nearest_good_tile(upper=chosen.is_upper,
                                                preserve_elevation=z)
            except IndexError:
                continue
            assert (self.x, self.y) != (chosen_x, chosen_y)
            assert (self.x, self.y) != (chosen.x, chosen.y)
            self._chocobo_rider = chosen
            chosen._chocobo_mount = self
            self.set_bit('enemy_team', chosen.get_bit('enemy_team'))
            self.set_bit('alternate_team', chosen.get_bit('alternate_team'))
            assert self.allegiance == self._chocobo_rider.allegiance
            return True
        self.x, self.y = (old_x, old_y)

    def check_no_collisions(self):
        if self.map is None:
            return True

        if self.is_present:
            for u in self.neighbors:
                if (u.is_present and u is not self
                        and (u.x, u.y) == (self.x, self.y)
                        and (u.is_important or self.is_important)):

                    if (u.x == u.old_data['x'] and u.y == u.old_data['y']
                            and self.x == self.old_data['x']
                            and self.y ==  self.old_data['y']
                            and u.presence == u.presence_old
                            and self.presence == self.presence_old):
                        continue
                    return False
        return True

    def preclean(self):
        self.fix_palette()

        if (self.is_chocobo and self.encounter is not None
                and self.encounter.num_characters > 0
                and self.get_bit('always_present')):
            self.attempt_chocobo_knight()

        if self.is_important and self.map is not None:
            badness = self.map.get_tile_attribute(
                self.x, self.y, 'bad_regardless',
                upper=self.is_upper, singleton=True)
            try:
                replaced_map = hasattr(self.map, '_loaded_from')
                semibad = isinstance(badness, set) and True in badness
                if badness is not False:
                    assert (self.x == self.old_data['x'] and
                            self.y == self.old_data['y'] and
                            self.map == self.old_map and
                            (semibad or not replaced_map)
                            and hasattr(self, '_fixed_initial_coordinates')
                            and self._fixed_initial_coordinates)
            except AssertionError:
                self.relocate_nearest_good_tile()
                return self.preclean()

        assert self.check_no_collisions()

        if (self.encounter and self.encounter.num_characters and
                self.entd.is_valid and self.is_present
                and not self.get_bit('enemy_team')):
            boost = random.randint(0, 3) + random.randint(0, 3)
            boost = int(round(mutate_normal(
                0.5, 0, 1, return_float=True,
                random_degree=self.random_degree ** 0.5) * 6))
            if self.entd_index not in ENTDObject.NERF_ENTDS:
                self.normalize_level(boost)

        if (self.entd_index in ENTDObject.NERF_ENTDS
                and self.get_bit('enemy_team')):
            self.level = min(self.level, self.old_data['level'])
            if self.level >= 100:
                self.level = 1
            self.secondary = 0
            for attr in (['reaction', 'support', 'movement']
                         + UnitObject.EQUIPMENT_ATTRS):
                if attr == 'righthand':
                    continue
                if random.choice([True, False]):
                    setattr(self, attr, 0)

        if (self.graphic != self.old_data['graphic']
                and self.is_valid and not self.has_generic_sprite
                and self.entd_index not in ENTDObject.LUCAVI_ENTDS):
            if random.random() < (self.random_degree ** 0.85) / 2:
                self.set_bit('join_after_event', True)

        if not self.is_canonical:
            for attr in ['brave', 'faith', 'month', 'day']:
                setattr(self, attr, getattr(self.canonical_relative, attr))

        if self.job.character_name == 'Ramza':
            self.set_bit('join_after_event',
                         self.get_bit('join_after_event', old=True))
            if self.entd_index not in UnitObject.CHANGED_RAMZA_ENTD_INDEXES:
                for attr in self.old_data:
                    if attr in ('x', 'y', 'facing'):
                        continue
                    setattr(self, attr, self.old_data[attr])

    def cleanup(self):
        for equip in UnitObject.EQUIPMENT_ATTRS:
            if (self.old_data['graphic'] == self.MONSTER_GRAPHIC
                    and self.entd.is_valid and not self.is_monster
                    and getattr(self, equip) in (0, 0xff)):
                setattr(self, equip, 0xfe)

        for attr in ['reaction', 'support', 'movement']:
            if getattr(self, attr) in JobObject.BANNED_RSMS:
                setattr(self, attr, 0x1fe)

            fixed_attr = '_fixed_unit_%s' % attr
            if hasattr(self.job, fixed_attr):
                setattr(self, attr, getattr(self.job, fixed_attr))

        assert self.check_no_collisions()
        if self.unit_id not in (0, 0xff):
            for u in self.neighbors:
                if u is self:
                    continue
                if (self.unit_id == self.old_data['unit_id']
                        and u.unit_id == u.old_data['unit_id']):
                    continue
                assert u.unit_id != self.unit_id

        if self.is_important and self.encounter is not None:
            assert 0 <= self.x < self.map.width
            assert 0 <= self.y < self.map.length

        if self.index == 0x1494 and get_global_label() == 'FFT_TLW':
            pass
        else:
            assert (0 <= self.unlocked <=
                    JobObject.MIME_INDEX - JobObject.SQUIRE_INDEX)

        if (self.character_name == 'Alma'
                and self.graphic == self.old_data['graphic']):
            altima = [u for u in ENTDObject.get(ENTDObject.FINAL_BATTLE).units
                      if u.job.index == JobObject.ALTIMA_PERFECT_BODY][0]
            if SkillsetObject.get(altima.secondary).is_generic:
                self.secondary = altima.secondary
                self.unlocked = altima.unlocked
                self.unlocked_level = altima.unlocked_level

        if (self.entd_index in ENTDObject.WIEGRAF and
                self.has_generic_sprite and self.get_gender() == 'male'):
            self.clear_gender()
            self.set_bit('female', True)

        if self.graphic in self.GENERIC_GRAPHICS:
            if self.job.name == 'dancer' and self.get_gender() == 'male':
                self.clear_gender()
                self.set_bit('female', True)
            if self.job.name == 'bard' and self.get_gender() == 'female':
                if self.entd_index not in ENTDObject.WIEGRAF:
                    self.clear_gender()
                    self.set_bit('male', True)
            if self.get_gender() == 'male':
                self.graphic = self.MALE_GRAPHIC
            if self.get_gender() == 'female':
                self.graphic = self.FEMALE_GRAPHIC

        if (self.entd_index == ENTDObject.ORBONNE_OPENING_ENTD
                and not self.get_bit('enemy_team')):
            self.set_bit('control', True)

        if (self.entd_index in ENTDObject.ORBONNES
                and self.entd_index != ENTDObject.ORBONNE_OPENING_ENTD
                and self.character_name != 'Ramza'):
            units = ENTDObject.get(ENTDObject.ORBONNE_OPENING_ENTD).units
            for u in units:
                if u.character_name == self.character_name:
                    for attr in ('unlocked', 'unlocked_level', 'secondary',
                                 'reaction', 'support', 'movement',
                                 'head', 'body', 'accessory',
                                 'righthand', 'lefthand', 'job_index',
                                 'level', 'month', 'day', 'brave', 'faith'):
                        setattr(self, attr, getattr(u, attr))

        if self.job.is_lucavi and self.is_valid and not self.job.is_altima:
            if UnitObject.flag in get_flags():
                assert 1 <= self.secondary <= 0xfd
            else:
                assert self.secondary == self.old_data['secondary']
            if not SkillsetObject.get(self.secondary).is_lucavi_appropriate:
                self.secondary = 0

        if (self.entd.index in ENTDObject.DEEP_DUNGEON or (
                self.unit_id > 0 and self.encounter
                and self.entd.index != ENTDObject.ENDING
                and self.unit_id in self.encounter.movements)):
            self.set_bit('always_present',
                         self.get_bit('always_present', old=True))
            self.set_bit('randomly_present',
                         self.get_bit('randomly_present', old=True))

        old_pos = self.old_data['x'], self.old_data['y'], self.is_upper_old
        new_pos = self.x, self.y, self.is_upper
        if (new_pos != old_pos
                and hasattr(self, '_fixed_initial_coordinates')
                and self._fixed_initial_coordinates):
            if hasattr(self.map, '_loaded_from'):
                old_x, old_y = self.old_data['x'], self.old_data['y']
                tiles = self.map.get_tiles_compare_attribute(
                    'bad_regardless', False, upper=self.is_upper_old)
                assert self.map.index == self.old_map.index
                assert (old_x, old_y) not in tiles
            else:
                raise Exception('Unit must retain initial coordinates.')

        if 'easymodo' in get_activated_codes() and self.get_bit('enemy_team'):
            self.level = 1


class TrophyObject(TableObject):
    flag = 't'
    custom_random_enable = flag

    @property
    def unit(self):
        return UnitObject.get(self.index)

    def mutate(self):
        gil = self.unit.gil
        gil = mutate_normal(gil, 0, 0xff, random_degree=self.random_degree)
        self.unit.gil = gil

        trophy_index = self.unit.trophy
        if 1 <= trophy_index <= 0xfd:
            trophy = ItemObject.get(
                trophy_index).get_similar(random_degree=self.random_degree,
                                          wide=True)
            self.unit.trophy = trophy.index


class ENTDObject(TableObject):
    flag = 'u'
    custom_random_enable = flag

    NAMED_GENERICS = {}

    @classmethod
    def set_class_constants(self):
        if get_global_label() == 'FFT_TLW':
            valid = [0x10a, 0x10b, 0x10d, 0x101, 0x104, 0x106, 0x109, 0x10c,
                     0x102, 0x107, 0x10e, 0x110, 0x111, 0x112, 0x107, 0x115,
                     0x117, 0x119, 0x182, 0x11d, 0x11e, 0x11f, 0x120, 0x121,
                     0x122, 0x124, 0x128, 0x12a, 0x12b, 0x12c, 0x12f, 0x130,
                     0x133, 0x135, 0x138, 0x139, 0x187, 0x13b, 0x13c, 0x13e,
                     0x13f, 0x140, 0x143, 0x146, 0x147, 0x148, 0x14a, 0x14b,
                     0x14d, 0x14f, 0x151, 0x152, 0x153, 0x179, 0x17a, 0x17b,
                     0x17c, 0x17d, 0x17e, 0x17f, 0x157, 0x158, 0x15a, 0x15c,
                     0x15d, 0x15e, 0x160, 0x161, 0x163, 0x165, 0x166, 0x167,
                     0x169, 0x16a, 0x16b, 0x16d, 0x16e, 0x16f, 0x173, 0x175,
                     0x176, 0x177, 0x18a, 0x18b, 0x18c, 0x18d, 0x190, 0x18f]
            valid += [0x134, 0x141, 0x149, 0x16c, 0x192, 0x196, 0x198, 0x19a]
            valid += lange(0x19b, 0x1b9)
            self.VALID_INDEXES = sorted(set(
                lange(1, 9) + lange(0xd, 0x21) + lange(0x25, 0x2d) +
                lange(0x31, 0x45) + lange(0x49, 0x51) + lange(0x52, 0xfd) +
                valid))
            self.LAST_NONTEST = 0x1cb

            self.DEEP_DUNGEON = set(
                [0x182] +
                lange(0xb1, 0xb5) + lange(0xc9, 0xcd) +
                lange(0xd5, 0xd9) + lange(0xe1, 0xfd))
            self.LUCAVI_ENTDS = {0x135, 0x14f, 0x17f, 0x16d, 0x173}
            self.SPECIAL_CASE_SPRITES = self.LUCAVI_ENTDS | self.DEEP_DUNGEON
            self.WIEGRAF = {0x117, 0x1a8, 0x14f}
            self.VELIUS = 0x14f

            self.FINAL_BATTLE = 0x17f
            self.CEMETARY = 0x180
            self.ENDING = 0x181
            self.ORBONNES = {0x11b, 0x11c, 0x101}
            self.ORBONNE_OPENING_ENTD = 0x101

            self.MUROND_HOLY_PLACE = 0x175

            self.NERF_ENTDS = {0x10a, 0x101, 0x104, 0x106}
            return

        self.VALID_INDEXES = (
            lange(1, 9) + lange(0xd, 0x21) + lange(0x25, 0x2d) +
            lange(0x31, 0x45) + lange(0x49, 0x51) + lange(0x52, 0xfd) +
            lange(0x180, 0x1d6))
        self.LAST_NONTEST = 0x1d5

        self.DEEP_DUNGEON = set(
                [0x192] +
                lange(0xb1, 0xb5) + lange(0xc9, 0xcd) +
                lange(0xd5, 0xd9) + lange(0xe1, 0xfd))
        self.LUCAVI_ENTDS = {0x1a0, 0x1b0, 0x1b9, 0x1c9, 0x1cb}
        self.SPECIAL_CASE_SPRITES = self.LUCAVI_ENTDS | self.DEEP_DUNGEON
        self.WIEGRAF = {0x190, 0x1a8, 0x1b0}
        self.VELIUS = 0x1b0

        self.FINAL_BATTLE = 0x1b9
        self.CEMETARY = 0x134
        self.ENDING = 0x133
        self.ORBONNES = {0x110, 0x183}
        self.ORBONNE_OPENING_ENTD = 0x183

        self.MUROND_HOLY_PLACE = 0x1cc

        self.NERF_ENTDS = {0x180, 0x183, 0x184, 0x185}

    def read_data(self, filename=None, pointer=None):
        if not hasattr(ENTDObject, 'FINAL_BATTLE'):
            ENTDObject.set_class_constants()
        super().read_data(filename, pointer)

    @classproperty
    def after_order(self):
        return [JobReqObject]

    @classmethod
    def get_unused(self):
        unused = sorted(set(range(0x100, 0x200)) -
                        {enc.entd_index for enc in EncounterObject.every})
        unused = [ENTDObject.get(i) for i in unused]
        unused = [e for e in unused if not e.is_valid]
        if get_global_label() == 'FFT_TLW':
            unused = [e for e in unused if e.index > self.LAST_NONTEST]
        return unused[-1]

    @cached_property
    def units(self):
        return [UnitObject.get((self.index << 4) | i) for i in range(0x10)]

    @property
    def unit_signature(self):
        units = [u for u in self.units
                 if u.is_present_old or u.has_unique_name]
        ss = []
        for u in units:
            if u.old_data['graphic'] < 0x80:
                ss.append('s{0:0>2X}'.format(u.old_data['graphic']))
            else:
                ss.append('j{0:0>2X}'.format(u.old_data['job_index']))
        return ','.join(ss)

    @cached_property
    def avg_level(self):
        levels = [u.old_data['level'] for u in self.units
                  if u.is_present_old and 1 <= u.old_data['level'] <= 99
                  and (u.get_bit('join_after_event', True) or not u.is_ally)]
        if not levels:
            return None
        highest = max(levels)
        avg = sum(levels) / len(levels)
        return ((2*highest) + avg) / 3

    @cached_property
    def old_jobs(self):
        return [JobObject.get(u.old_data['job_index']) for u in self.units
                if u.is_present_old]

    @cached_property
    def is_valid(self):
        return self.index in self.VALID_INDEXES

    @clached_property
    def valid_entds(self):
        return [e for e in self.every if e.is_valid]

    @property
    def present_units(self):
        return [u for u in self.units if u.is_present]

    @property
    def sprites(self):
        return {u.sprite_id for u in self.present_units}

    @property
    def old_sprites(self):
        return {u.old_sprite_id for u in self.units if u.is_present_old}

    @cached_property
    def encounter(self):
        return self.units[0].encounter

    @property
    def has_chocobo_potential(self):
        if not self.is_valid:
            return False
        for u in self.units:
            if u.is_human and u.is_present and u.unit_id >= 0x80:
                return True
        return False

    @property
    def has_chocobo(self):
        return UnitObject.CHOCOBO_SPRITE_ID in self.available_sprites

    def add_units(self):
        if self.encounter is None or self.encounter.num_characters == 0:
            return

        templates = [u for u in self.present_units
                     if u.has_generic_sprite and not u.has_unique_name]
        if not templates:
            return

        spares = [u for u in self.units
                  if not (u.is_present or u.is_important)]
        while True:
            margin = len(spares) - self.encounter.num_characters
            if margin <= 0:
                return
            index = random.randint(0, margin)
            if index == 0:
                break

            chocobo = (self.has_chocobo_potential and self.has_chocobo
                       and random.random() < (self.random_degree ** 0.25)
                       and random.choice([True, False]))

            if chocobo or random.random() < self.random_degree:
                spare = spares.pop()
                template = random.choice(templates)
                for attr in template.old_data:
                    template_value = template.old_data[attr]
                    if (attr in UnitObject.EQUIPMENT_ATTRS + ['secondary']
                            and template_value in (0, 0xff)):
                        setattr(spare, attr, 0xfe)
                    elif (attr in ('reaction', 'support', 'movement')
                            and template_value in (0, 0x1ff)):
                        setattr(spare, attr, 0x1fe)
                    else:
                        setattr(spare, attr, template_value)
                spare.unit_id = 0x90 | (spare.index % 0x10)
                spare.set_bit('always_present', True)
                spare.clear_cache()
                if self.index in self.NERF_ENTDS:
                    spare.set_bit('enemy_team', False)
                    spare.set_bit('alternate_team', False)
                else:
                    spare.randomize_allegiance()
                spare.find_appropriate_position()
                if chocobo:
                    chocobo = random.choice(UnitObject.chocobo_pool)
                    spare._target_sprite = (
                        chocobo.old_data['graphic'], chocobo.old_job.index,
                        'monster')
            else:
                break

    def randomize_sprites(self):
        present_units = [u for u in self.present_units
                         if not hasattr(u, '_target_sprite')]
        old_sprites = [u.old_sprite_id for u in present_units]
        preset_sprites = {u._target_sprite for u in self.units
                          if hasattr(u, '_target_sprite')
                          and isinstance(u._target_sprite, UnitObject)}
        special_units = [u for u in present_units
                         if not u.has_generic_sprite]
        special_names = [u.character_name for u in special_units]
        named_generics = [u for u in present_units
                          if u.has_unique_name and u.has_generic_sprite]
        generic_units = [u for u in present_units
                         if u.has_generic_sprite and not u.has_unique_name]

        new_sprites = {u.old_sprite_id for u in special_units
                       if not hasattr(u, '_target_sprite')}
        available_sprites = set()
        temp_named = {}
        for u in named_generics:
            assert not hasattr(u, '_target_sprite')
            key = (u.character_name, u.old_sprite_id)
            if u.old_sprite_id in temp_named:
                new_sprite = temp_named[u.old_sprite_id]
            elif key in self.NAMED_GENERICS:
                new_sprite = self.NAMED_GENERICS[key]
            else:
                if u.get_bit('enemy_team'):
                    new_sprite = u.get_similar_sprite(
                        exclude_sprites=new_sprites, random_degree=1.0)
                else:
                    new_sprite = u.get_similar_sprite(
                        exclude_sprites=new_sprites)

            old_g, old_j = u.old_sprite_id
            new_g, new_j = new_sprite
            if new_g == UnitObject.MONSTER_GRAPHIC:
                candidates = [
                    j for j in JobObject.every if j.monster_portrait == new_j]
                chosen = random.choice(candidates)
                u._target_sprite = (old_g, chosen.index, u.get_gender())
            else:
                u._target_sprite = (old_g, new_j, u.get_gender())

            new_sprite = old_g, new_j
            if u.old_sprite_id not in temp_named:
                temp_named[u.old_sprite_id] = new_sprite
            assert temp_named[u.old_sprite_id] == new_sprite
            if key not in self.NAMED_GENERICS:
                self.NAMED_GENERICS[key] = new_sprite
            assert self.NAMED_GENERICS[key] == new_sprite
            new_sprites.add(new_sprite)

        special_sprites = set()
        while (len(new_sprites | special_sprites | preset_sprites)
                < len(self.old_sprites)):
            if not generic_units:
                break

            has_chocobo = (UnitObject.CHOCOBO_SPRITE_ID in
                           available_sprites | new_sprites)
            if self.is_valid and not has_chocobo:
                has_chocobo_potential = False
                for sprite in (sorted(available_sprites)
                               + sorted(special_sprites)):
                    if isinstance(sprite, UnitObject) and sprite.is_human:
                        has_chocobo_potential = True
                        break
                    if isinstance(sprite, tuple):
                        g, j = sprite
                        if g in UnitObject.GENERIC_GRAPHICS:
                            has_chocobo_potential = True
                            break
                if has_chocobo_potential:
                    u = random.choice(generic_units + [None])
                    if u is None:
                        new_sprite = UnitObject.CHOCOBO_SPRITE_ID
                        available_sprites.add(new_sprite)
                        new_sprites.add(new_sprite)
                        continue

            u = random.choice(generic_units)
            if (self.index not in self.NERF_ENTDS
                    and random.random() < self.random_degree
                    and random.choice([True, False])):
                new_sprite = u.get_special_sprite()
                if (self.index in self.WIEGRAF
                        and new_sprite.get_gender() == 'male'):
                    continue
                elif new_sprite.character_name not in special_names:
                    special_sprites.add(new_sprite)
            else:
                new_sprite = u.get_similar_sprite(exclude_sprites=new_sprites)
                available_sprites.add(new_sprite)
                assert new_sprite not in new_sprites
                new_sprites.add(new_sprite)

        assert not hasattr(self, 'available_sprites')
        self.available_sprites = sorted(available_sprites)
        self.available_sprites += sorted(special_sprites,
                                         key=lambda u: u.index)

        if (UnitObject.CHOCOBO_SPRITE_ID in old_sprites and
                self.available_sprites and not
                any([g == UnitObject.MONSTER_GRAPHIC
                     for (g, j) in available_sprites])):
            max_index = len(self.available_sprites) - 1
            index = random.randint(0, max_index)
            self.available_sprites[index] = UnitObject.CHOCOBO_SPRITE_ID

    def randomize_special(self):
        generic_units = [u for u in self.present_units
                         if u.get_bit('enemy_team')
                         and not u.job.has_unique_name]
        candidates = [u for u in UnitObject.special_unit_pool
                      if u.rank < self.rank or not u.job.is_lucavi]
        if self.index == self.VELIUS:
            candidates = [c for c in candidates
                          if c.get_gender() == 'female']

        sprite_ids = sorted({u.sprite_id for u in generic_units})
        for sprite_id in sprite_ids:
            if (self.index in self.DEEP_DUNGEON
                    and random.choice([True, False])):
                continue
            matching_units = [u for u in self.present_units
                              if u.sprite_id == sprite_id]
            templates = [u for u in matching_units if u.rank >= 0]
            if templates:
                template = random.choice(templates)
                chosen = template.get_similar(
                    candidates=candidates,
                    wide=True, override_outsider=True, presorted=True,
                    random_degree=UnitObject.random_degree)
            else:
                chosen = random.choice(candidates)
            for u in matching_units:
                u._target_sprite = chosen

    def randomize(self):
        super().randomize()
        if self.index in self.SPECIAL_CASE_SPRITES:
            self.randomize_special()
        self.randomize_sprites()
        if EncounterObject.flag in get_flags():
            self.add_units()

    def cleanup(self):
        assert len(self.sprites) <= max(len(self.old_sprites), 9)


TEST_PALETTE_INDEX = 2
class FormationPaletteObject(TableObject):
    @property
    def name(self):
        if not names.formpalettes[self.index].strip():
            return None
        return path.join(SANDBOX_PATH, 'BATTLE',
                         names.formpalettes[self.index])

    def cleanup(self):
        if DEBUG:
            self.colors[TEST_PALETTE_INDEX] = 0x7c1f


class FormationFacePaletteObject(TableObject):
    @property
    def name(self):
        if not names.formfacepalettes[self.index].strip():
            return None
        return path.join(SANDBOX_PATH, 'BATTLE',
                         names.formfacepalettes[self.index])


class FormationSpriteMetaObject(TableObject):
    @classproperty
    def after_order(self):
        return [SpriteMetaObject, SpriteImageObject]

    @property
    def name(self):
        if not names.formsprites[self.index].strip():
            return None
        return path.join(SANDBOX_PATH, 'BATTLE', names.formsprites[self.index])

    @property
    def image(self):
        if not self.name:
            return
        sio = SpriteImageObject.get_by_name(self.name)
        assert sio is not None
        return sio

    @property
    def sprite_meta(self):
        if not self.image:
            return None

        metas = [smo for smo in SpriteMetaObject.every
                 if smo.old_image is self.image]
        temp = [m for m in metas
                if m.SQUIRE_INDEX <= m.index < m.TIAMAT_INDEX]
        if temp:
            metas = temp

        assert len(metas) == 1
        return metas[0]

    def write_unit_bin(self):
        meta = self.sprite_meta
        if meta.old_seq_name in ('CYOKO', 'RUKA'):
            return

        if hasattr(meta, '_loaded_from'):
            sprite_file = get_open_file(meta._loaded_from)
        else:
            sprite_file = get_open_file(meta.image.filename)
        sprite_file_image_offset = 0x200
        FULL_WIDTH = 0x100

        if meta.old_seq_name in ('TYPE1', 'TYPE2'):
            source_x = 0x26
            source_y = 0
            assert self.width == 0x18
        elif meta.old_seq_name == 'MON':
            source_x = 0x30 + ((0x30 - self.width) // 2)
            source_y = 0x30 - self.length
            assert self.width in (0x18, 0x30)
        else:
            raise Exception('Unsupported sprite type for UNIT.BIN: %s'
                            % meta.old_seq_name)

        target_x = self.x
        target_y = self.y
        if self.unknown >= 0x650000:
            target_y += 0x100
        width = self.width
        length = self.length

        unit_file = get_open_file(
            path.join(SANDBOX_PATH, 'EVENT', 'UNIT.BIN'))
        for y in range(length):
            sprite_index = ((FULL_WIDTH * (source_y + y)) + source_x) // 2
            sprite_index += sprite_file_image_offset
            sprite_file.seek(sprite_index)
            data = sprite_file.read(width // 2)
            unit_index = ((FULL_WIDTH * (target_y + y)) + target_x) // 2
            unit_file.seek(unit_index)
            unit_file.write(data)

        fps = [fp for fp in FormationPaletteObject.every
               if fp.name and fp.name.startswith(self.name)]
        for fp in fps:
            name, palette_index = fp.name.split(':')
            palette_index = int(palette_index)
            sprite_file.seek(palette_index * 0x20)
            palette = [int.from_bytes(sprite_file.read(2), byteorder='little')
                       for _ in range(16)]
            fp.colors = palette

    def write_wldface_bin(self):
        portrait_indexes = [
            i for i in range(len(names.formfaces))
            if names.formfaces[i] == names.formsprites[self.index]]
        assert len(portrait_indexes) <= 1
        if not portrait_indexes:
            return
        portrait_index = portrait_indexes[0]

        meta = self.sprite_meta
        if hasattr(meta, '_loaded_from'):
            sprite_file = get_open_file(meta._loaded_from)
        else:
            sprite_file = get_open_file(meta.image.filename)
        sprite_file_image_offset = 0x200
        FULL_WIDTH = 0x100

        source_x = 0x50
        source_y = 0x100
        width = 48
        length = 32

        portrait = []
        for y in range(length):
            sprite_index = ((FULL_WIDTH * (source_y + y)) + source_x) // 2
            sprite_index += sprite_file_image_offset
            sprite_file.seek(sprite_index)
            data = sprite_file.read(width // 2)
            pixels = []
            for c in data:
                pixels.append(c & 0xf)
                pixels.append(c >> 4)
            portrait.append(pixels)

        portrait = rot90(portrait)

        width = 32
        length = 48
        portraits_per_row = 8
        portraits_per_block = 40
        blocklength = 0x100
        block = portrait_index // portraits_per_block
        row = (portrait_index % portraits_per_block) // portraits_per_row
        column = portrait_index % portraits_per_row
        target_x = column * width
        target_y = (block * blocklength) + (row * length)
        face_file = get_open_file(
            path.join(SANDBOX_PATH, 'EVENT', 'WLDFACE.BIN'))
        for y in range(length):
            portrait_index = ((FULL_WIDTH * (target_y + y)) + target_x) // 2
            pixels = portrait[y]
            assert len(pixels) == width
            data = []
            for p1, p2 in zip(pixels[::2], pixels[1::2]):
                data.append(p1 | (p2 << 4))
            data = bytes(data)
            assert len(data) == width // 2
            face_file.seek(portrait_index)
            face_file.write(data)

        for i in range(3):
            sprite_file.seek((8 + i) * 0x20)
            palette = [int.from_bytes(sprite_file.read(2), byteorder='little')
                       for _ in range(16)]
            valid = []
            name = '{0}:{1}'.format(self.name, i)
            for ffp in FormationFacePaletteObject.every:
                if ffp.name == name:
                    ffp.colors = palette

    def cleanup(self):
        if self.name is not None:
            self.write_unit_bin()
            self.write_wldface_bin()


class SpritePointerObject(TableObject): pass


def get_palette_indexes_from_filename(filename):
    palettes = []
    done_palettes = set()
    with open(filename, 'rb') as f:
        for i in range(8):
            f.seek(i * 0x20)
            palette = [int.from_bytes(f.read(2), byteorder='little')
                       for _ in range(16)]
            if tuple(palette) not in done_palettes:
                palettes.append(palette)
                done_palettes.add(tuple(palette))
    return [i for (i, p) in enumerate(palettes) if len(set(p)) > 2]


def fill_empty_palettes(filename):
    valid_indexes = get_palette_indexes_from_filename(filename)
    if not valid_indexes:
        return

    chosen_index = min(valid_indexes)
    with open(filename, 'r+b') as f:
        f.seek(chosen_index * 0x20)
        chosen_palette = [int.from_bytes(f.read(2), byteorder='little')
                          for _ in range(16)]
        f.seek((chosen_index+8) * 0x20)
        chosen_portrait = [int.from_bytes(f.read(2), byteorder='little')
                           for _ in range(16)]
        for i in range(8):
            if i in valid_indexes:
                continue
            f.seek(i * 0x20)
            for color in chosen_palette:
                f.write(color.to_bytes(length=2, byteorder='little'))
            f.seek((i+8) * 0x20)
            for color in chosen_portrait:
                f.write(color.to_bytes(length=2, byteorder='little'))


class SpriteMetaObject(TableObject):
    SQUIRE_INDEX = 0x60
    CHOCOBO_INDEX = 0x86
    TIAMAT_INDEX = 0x95

    SEQ_NAMES = ['TYPE1', 'TYPE2', 'CYOKO', 'MON',
                 'N/A', 'RUKA', 'ARUTE', 'KANZEN']

    CUSTOM_SPRITES_PATH = path.join('custom', 'sprites')
    TAGS_FILEPATH = path.join(CUSTOM_SPRITES_PATH, 'tags.txt')
    WHITELIST = defaultdict(set)
    BLACKLIST = defaultdict(set)

    try:
        for line in read_lines_nocomment(TAGS_FILEPATH):
            assert ':' in line
            name, tags = line.split(':')
            name = name.strip()
            tags = tags.strip().split()
            for t in tags:
                assert t
                if t.startswith('!'):
                    BLACKLIST[name].add(t[1:])
                else:
                    WHITELIST[name].add(t)
    except FileNotFoundError:
        print('WARNING: File not found - {0}'.format(TAGS_FILEPATH))

    REPLACING_SPRITES = defaultdict(list)
    for parent, children, filenames in sorted(walk(CUSTOM_SPRITES_PATH)):
        seq_name = path.split(parent)[-1]
        for f in sorted(filenames):
            if f.upper().endswith('.SPR'):
                REPLACING_SPRITES[seq_name].append(path.join(parent, f))

    if not REPLACING_SPRITES:
        print('WARNING: No custom sprites found.')

    PALETTE_INDEXES = {}
    for seq_name in REPLACING_SPRITES:
        for f in REPLACING_SPRITES[seq_name]:
            PALETTE_INDEXES[f] = get_palette_indexes_from_filename(f)

    DONE_SPRITES = set()
    SPRITE_MAP = {}

    @classproperty
    def randomize_order(self):
        return sorted(self.every, key=lambda e: e.signature)

    @property
    def name(self):
        if not self.image:
            return 'N/A'

        name = self.image.filename
        head, tail = path.split(name)
        return tail

    @property
    def image(self):
        sp = self.sprite_pointer
        if (sp.sector == sp.old_data['sector']):
            return self.old_image

        sector = SpritePointerObject.get(self.index).sector
        if sector == 0:
            return

        images = [sio for sio in SpriteImageObject.every
                  if sio.sector == sector]
        if not images:
            return
        assert len(images) == 1

        return images[0]

    @cached_property
    def old_image(self):
        sector = SpritePointerObject.get(self.index).old_data['sector']
        if sector == 0:
            return

        images = [sio for sio in SpriteImageObject.every
                  if sio.sector == sector]
        assert len(images) == 1
        return images[0]

    @property
    def seq_name(self):
        return self.SEQ_NAMES[self.seq]

    @property
    def old_seq_name(self):
        return self.SEQ_NAMES[self.old_data['seq']]

    @property
    def sprite_pointer(self):
        return SpritePointerObject.get(self.index)

    @property
    def required_palettes(self):
        if hasattr(self, '_required_palettes'):
            return self._required_palettes

        for smo in SpriteMetaObject.every:
            smo._required_palettes = set()

        generic_palettes = set()
        generic_monster_palettes = {0, 1, 2}
        for u in UnitObject.every:
            if (u.is_valid or u.is_present
                    and u.entd.index <= ENTDObject.LAST_NONTEST):
                graphic = u.old_data['graphic']
                smo = None
                if 1 <= graphic < 0x80:
                    smo = SpriteMetaObject.get(graphic)
                    smo._required_palettes.add(0)
                elif graphic in UnitObject.GENERIC_GRAPHICS:
                    generic_palettes.add(u.old_data['palette'])
                elif graphic == UnitObject.MONSTER_GRAPHIC:
                    index = u.old_job.monster_portrait
                    if index > self.TIAMAT_INDEX:
                        smo = SpriteMetaObject.get(index)
                        if 0 <= u.old_data['palette'] <= 2:
                            smo._required_palettes.add(u.old_data['palette'])
                elif graphic != 0:
                    raise Exception('Unknown graphic index.')

        by_name = defaultdict(set)
        for smo in SpriteMetaObject.every:
            if smo.SQUIRE_INDEX <= smo.index < smo.CHOCOBO_INDEX:
                by_name[smo.name] |= generic_palettes
            elif smo.CHOCOBO_INDEX <= smo.index <= smo.TIAMAT_INDEX:
                by_name[smo.name] |= generic_monster_palettes

        for smo in SpriteMetaObject.every:
            smo._required_palettes = sorted(by_name[smo.name])

        return self.required_palettes

    def get_compatible_with(self, image_path):
        head, image_tail = path.split(image_path)
        image_white_tags = self.WHITELIST[image_tail]
        image_black_tags = self.BLACKLIST[image_tail]

        head, self_tail = path.split(self.name)
        self_white_tags = self.WHITELIST[self_tail]
        self_black_tags = self.BLACKLIST[self_tail]

        if (image_white_tags & self_black_tags
                or image_black_tags & self_white_tags):
            return False

        if ((image_white_tags or self_white_tags)
                and not (image_white_tags & self_white_tags)):
            return False

        if len(self.required_palettes) <= 1:
            return True

        if image_path in self.PALETTE_INDEXES:
            image_palettes = set(self.PALETTE_INDEXES[image_path])
        else:
            image = SpriteImageObject.get_by_name(image_path)
            image_palettes = set(image.valid_palette_indexes)
        return set(self.required_palettes) <= image_palettes

    @cached_property
    def is_valid_replacement(self):
        if not self.old_image:
            return False
        if not self.required_palettes:
            return False
        if self.old_image.size < 43008:
            return False
        return True

    @property
    def swap_candidates(self):
        if self.seq_name in ['TYPE1', 'TYPE2']:
            allowed_seqs = ('TYPE1', 'TYPE2')
        else:
            allowed_seqs = (self.seq_name,)

        candidates = [c for seq_name in allowed_seqs
                      for c in self.REPLACING_SPRITES[seq_name]]
        if 'novanilla' not in get_activated_codes():
            candidates += [smo.image.filename for smo in SpriteMetaObject.every
                           if smo.image and smo.is_valid_replacement
                           and smo.old_seq_name in allowed_seqs]

        if self.image.filename not in candidates:
            candidates.append(self.image.filename)

        candidates = [c for c in candidates if self.get_compatible_with(c)]
        return candidates

    def randomize(self):
        if 'partyparty' not in get_activated_codes():
            return

        if not self.image:
            return

        old_name = self.name
        if old_name in self.SPRITE_MAP:
            chosen = self.SPRITE_MAP[old_name]
        else:
            candidates = self.swap_candidates
            candidates = [c for c in candidates if c not in self.DONE_SPRITES]
            if not candidates:
                return
            chosen = random.choice(sorted(set(candidates)))

        sio = SpriteImageObject.get_by_name(chosen)
        assert self.sprite_pointer.sector == self.image.sector
        assert self.sprite_pointer.sprite_size == self.image.size
        if sio is not None:
            old_smos = [smo for smo in SpriteMetaObject.every
                        if smo.old_image is sio]
            assert len({smo.old_data['seq'] for smo in old_smos}) == 1
            old_smo = old_smos[0]
            if old_smo.old_seq_name != self.seq_name:
                assert ({self.seq_name, old_smo.old_seq_name}
                        == {'TYPE1', 'TYPE2'})
                self.seq = old_smo.old_data['seq']
            assert self.seq_name == old_smo.old_seq_name
            old_name = self.name
            self.sprite_pointer.sector = sio.sector
            self.sprite_pointer.sprite_size = sio.size
            assert self.sprite_pointer.sector == self.image.sector
            assert self.sprite_pointer.sprite_size == self.image.size
        else:
            psx_fm = get_psx_file_manager()
            psx_fm.SKIP_REALIGNMENT = True
            template = psx_fm.get_file(self.image.filename)
            assert template
            new_name = 'RND{0:0>2X}.SPR'.format(self.index)
            new_path = path.join(template.dirname, new_name)
            assert not hasattr(self, '_loaded_from')
            self._loaded_from = new_path
            copyfile(chosen, new_path)
            fill_empty_palettes(new_path)
            imported = psx_fm.import_file(new_name, filepath=new_path,
                                          template=template)
            self.sprite_pointer.sector = imported.target_sector
            self.sprite_pointer.sprite_size = imported.filesize
            if self.seq_name in ('TYPE1', 'TYPE2'):
                if chosen in self.REPLACING_SPRITES['TYPE1']:
                    assert chosen not in self.REPLACING_SPRITES['TYPE2']
                    self.seq = self.SEQ_NAMES.index('TYPE1')
                    assert self.seq_name == 'TYPE1'
                elif chosen in self.REPLACING_SPRITES['TYPE2']:
                    assert chosen not in self.REPLACING_SPRITES['TYPE1']
                    self.seq = self.SEQ_NAMES.index('TYPE2')
                    assert self.seq_name == 'TYPE2'
                else:
                    raise Exception('Wrong SEQ type.')
            else:
                assert chosen in self.REPLACING_SPRITES[self.seq_name]
            assert self.image is None

        self.DONE_SPRITES.add(chosen)
        self.SPRITE_MAP[old_name] = chosen

    def cleanup(self):
        if self.seq_name in ('TYPE1', 'TYPE2'):
            assert self.old_data['seq'] == self.old_data['shp']
        if self.old_data['seq'] == self.old_data['shp']:
            self.shp = self.seq


class SpriteImageObject(TableObject):
    @property
    def palettes(self):
        if hasattr(self, '_palettes'):
            return self._palettes

        self._palettes = []
        f = get_open_file(self.filename)
        for i in range(8):
            f.seek(i * 0x20)
            palette = [int.from_bytes(f.read(2), byteorder='little')
                       for _ in range(16)]
            self._palettes.append(palette)

        return self.palettes

    @property
    def valid_palette_indexes(self):
        indexes = [i for i in range(8) if len(set(self.palettes[i])) > 2]
        unique_palettes = {tuple(self.palettes[i]) for i in range(8)}
        if len(unique_palettes) < len(indexes):
            indexes = indexes[:len(unique_palettes)]
        return indexes

    @cached_property
    def sector(self):
        filename = self.filename
        if filename.startswith(SANDBOX_PATH):
            filename = filename[len(SANDBOX_PATH):]
            filename = filename.lstrip(path.sep)
        psx_fm = get_psx_file_manager()
        sector = psx_fm.get_file(filename).target_sector
        return sector

    @cached_property
    def size(self):
        f = get_open_file(self.filename)
        f.seek(0)
        data = f.read()
        assert not len(data) % 0x800
        return len(data)

    @classmethod
    def get_by_name(self, name):
        for sio in SpriteImageObject.every:
            if name == sio.filename:
                return sio

    def cleanup(self):
        if not self.valid_palette_indexes:
            return
        f = get_open_file(self.filename)
        chosen_index = min(self.valid_palette_indexes)
        chosen_palette = self.palettes[chosen_index]
        assert len(set(chosen_palette)) > 2
        for i in range(8):
            f.seek(i * 0x20)
            if i in self.valid_palette_indexes:
                continue
            for color in chosen_palette:
                f.write(color.to_bytes(length=2, byteorder='little'))


def load_event_patch(filename):
    patches = {}
    key = None
    for line in read_lines_nocomment(filename):
        while '  ' in line:
            line = line.replace('  ', ' ')
        if line[0] == '!':
            _, name, index, pointer, _ = line.split()
            index, pointer = int(index, 0x10), int(pointer, 0x10)
            key = (name, index, pointer)
            patches[key] = ''
        else:
            patches[key] += line + '\n'

    for key in sorted(patches):
        name, index, pointer = key
        obj = [o for o in ALL_OBJECTS if o.__name__ == name][0]
        obj = obj.get(index)
        assert obj.pointer == pointer
        obj.load_patch(patches[key].strip())


def replace_ending():
    load_event_patch(path.join(tblpath, 'patch_ending.txt'))
    encounter = EncounterObject.get(EncounterObject.ENDING)
    encounter.following = 0
    encounter.music = encounter.ENDING_MUSIC
    delita = [u for u in encounter.units if u.character_name == 'Delita'][0]
    ovelia = [u for u in encounter.units if u.character_name == 'Ovelia'][0]
    chocobo = [u for u in encounter.units
               if u.old_sprite_id == UnitObject.CHOCOBO_SPRITE_ID][0]
    chocobo.set_sprite(UnitObject.CHOCOBO_SPRITE_ID)
    ramza = [u for u in encounter.units if u.character_name == 'Ramza'][0]
    ramza.set_bit('always_present', False)
    ramza.set_bit('load_formation', True)
    ramza.set_bit('control', True)
    ramza.set_bit('enemy_team', False)
    delita.set_bit('enemy_team', True)
    chocobo.unknown4 = 0x400
    ovelia.unknown4 = 0x400
    chocobo.behavior = 8
    ovelia.behavior = 8
    delita.behavior = 0x58
    ramza.unit_id = 3
    delita.target_id = ramza.unit_id

    if delita.job.immune_status & JobObject.INVITE_STATUS:
        delita.job.immune_status ^= JobObject.INVITE_STATUS
    generic_skillsets = [ss for ss in SkillsetObject.every if ss.is_generic
                         and AbilityObject.INVITATION in ss.action_indexes]
    if not generic_skillsets:
        skillset = SkillsetObject.get(ramza.job.skillset_index)
        indexes = [i for i in skillset.action_indexes if i > 0]
        if AbilityObject.INVITATION not in indexes:
            while len(indexes) >= 16:
                chosen = random.choice(indexes)
                indexes.remove(chosen)
            skillset.set_actions(indexes + [AbilityObject.INVITATION])

    knives = range(1, 0x0B)
    knives = [k for k in ItemObject.ranked if k.index in knives]
    for attr in ["lefthand", "righthand", "head", "body", "accessory"]:
        setattr(delita, attr, 0xFE)
        setattr(ovelia, attr, 0xFE)
        setattr(chocobo, attr, 0)
    ovelia.righthand = random.choice(knives).index

    entd = ENTDObject.get(ENTDObject.FINAL_BATTLE)
    henchmen = [u for u in entd.units if 3 <= u.index % 0x10 <= 6]
    assert len(henchmen) == 4
    assert len({u.sprite_id for u in henchmen}) == 1
    used_graphics = sorted(set([
        u.sprite_id for u in UnitObject.every if u.is_valid and u.is_present
        and u.sprite_id not in henchmen and not u.has_generic_sprite]))
    chosen = random.sample(used_graphics, 4)
    priest_sprite, other_sprites = (chosen[0], chosen[1:])
    other_sprites += [u.sprite_id for u in henchmen]
    assert len(other_sprites) == 7
    random.shuffle(other_sprites)

    cemetary = ENTDObject.get(ENTDObject.CEMETARY)
    other_units = [u for u in cemetary.units if 1 <= u.index % 0x10 <= 7]
    priest = cemetary.units[8]
    assert priest.index % 0x10 == 8
    for u, g in zip(other_units, other_sprites):
        u.set_sprite(g)
    priest.set_sprite(priest_sprite)


def add_bonus_battles():
    load_event_patch(path.join(tblpath, 'patch_bonus.txt'))
    warjilis_monsters = random.choice([True, False])
    WorldConditionalObject.get(WorldConditionalObject.WARJILIS).insert_bonus(
        map_index=GNSObject.WARJILIS, monsters=warjilis_monsters)
    WorldConditionalObject.get(WorldConditionalObject.ZARGHIDAS).insert_bonus(
        map_index=GNSObject.ZARGHIDAS, monsters=not warjilis_monsters)


def handle_patches():
    if get_global_label() == 'FFT_TLW':
        print('WARNING: RCTCR event patches not implemented for The Lion War.')
        return
    load_event_patch(path.join(tblpath, 'patch_fur_shop_from_start.txt'))
    load_event_patch(
        path.join(tblpath, 'patch_propositions_from_start.txt'))
    load_event_patch(
        path.join(tblpath, 'patch_battle_conditionals_base.txt'))
    replace_ending()

    if 'murond_exit_patch.txt' in get_activated_patches():
        load_event_patch(path.join(tblpath, 'patch_gauntlet.txt'))

    add_bonus_battles()


def write_spoiler(all_objects):
    spoiler_filename = 'fftr_spoiler_{0}.txt'.format(get_seed())

    f = open(spoiler_filename, 'w+')

    f.write('{0} v{1} {2} {3} {4} {5}\n'.format(
        get_global_label(), VERSION, get_flags(), get_seed(),
        get_random_degree()**0.5, get_difficulty()))

    all_objects = sorted(all_objects, key=lambda x: x.__name__)
    random_degrees = [(o.random_degree**0.5) for o in all_objects]
    if len(set(random_degrees)) > 1:
        f.write('R:{0}\n'.format(' '.join('%s' % rd for rd in random_degrees)))
    random_diffs = [o.random_difficulty for o in all_objects]
    if len(set(random_diffs)) > 1:
        f.write('D:{0}\n'.format(' '.join('%s' % rd for rd in random_diffs)))

    f.write('\n' + JobReqObject.jobtree + '\n\n')
    generics = [j for j in JobObject.every if j.is_generic]
    if JobObject.TLW_DARK_KNIGHTS:
        j = JobObject.get(min(JobObject.TLW_DARK_KNIGHTS))
        assert j not in generics
        generics.append(j)
    generics = sorted(generics, key=lambda j: j.name)

    for j in generics:
        f.write(j.profile + '\n\n')

    for p in PoachObject.every:
        f.write(str(p) + '\n')

    f.close()


if __name__ == '__main__':
    try:
        print('FINAL FANTASY TACTICS Rumble: Chaos: >>The Crashdown<< REMAKE'
              '\nRandomizer version %s.\n' % VERSION)

        ALL_OBJECTS = [g for g in globals().values()
                       if isinstance(g, type) and issubclass(g, TableObject)
                       and g not in [TableObject]]
        codes = {
            'novanilla': ['novanilla'],
            'bigtide': ['bigtide'],
            'easymodo': ['easymodo'],
            'partyparty': ['partyparty'],
            }
        run_interface(ALL_OBJECTS, snes=False, codes=codes,
                      custom_degree=True, custom_difficulty=True)

        for code in sorted(codes):
            if code in get_activated_codes():
                print('%s code activated!' % code.upper())

        if get_global_label() != 'FFT_TLW':
            xml_directory, xml_config = path.split(XML_PATCH_CONFIG_FILEPATH)
            xml_patches = xml_patch_parser.get_patches(xml_directory,
                                                       xml_config)
            for p in xml_patches:
                xml_patch_parser.patch_patch(SANDBOX_PATH, p)
        else:
            print('WARNING: XML patches not implemented for The Lion War.')

        handle_patches()

        clean_and_write(ALL_OBJECTS)

        if get_global_label() != 'FFT_TLW':
            for p in xml_patches:
                xml_patch_parser.patch_patch(SANDBOX_PATH, p, verify=True)

        write_spoiler(ALL_OBJECTS)
        write_cue_file()
        finish_interface()

    except Exception:
        print(format_exc())
        input('Press Enter to close this program. ')
