from randomtools.tablereader import (
    TableObject, addresses, names, get_activated_patches, get_open_file,
    mutate_normal, get_seed, get_global_label, tblpath,
    get_random_degree, get_difficulty, write_patch,
    SANDBOX_PATH)
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
from os import path, walk, environ
from string import digits, ascii_lowercase, ascii_uppercase
from sys import argv
from traceback import format_exc

import re


VERSION = '1'
ALL_OBJECTS = None
DEBUG = environ.get('DEBUG')

XML_PATCH_CONFIG_FILEPATH = path.join('custom', 'xml_patches', 'patches.cfg')


def lange(*args):
    return list(range(*args))


def hashstring(s):
    return md5(s.encode('ascii')).hexdigest()


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
    PARASITE = 0x164
    CHARGE_20 = 0x19d
    BALL = 0x189
    JUMPS = lange(0x18a, 0x196)
    MP_SWITCH = 0x1bd
    SHORT_CHARGE = 0x1e2
    NON_CHARGE = 0x1e3
    TELEPORT2 = 0x1f3
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
        if self.index > self.PARASITE:
            return None
        return AbilityAttributesObject.get(self.index)

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
        if self.index == self.TELEPORT2:
            self.jp_cost = 9999
            self.old_data['jp_cost'] = self.jp_cost

    @property
    def restores_mp(self):
        return self.index in self.MP_RESTORE_INNATES

    def cleanup(self):
        if self.jp_cost != 9999:
            self.jp_cost = round(self.jp_cost, -1)


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
    flag_description = 'ability/weapon status effects and procs'
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

    ARC_WITCH = 0x21
    ALTIMA_NICE_BODY = 0x41
    ALTIMA_PERFECT_BODY = 0x49

    VALID_INNATE_STATUSES = 0xcafce12a10
    VALID_START_STATUSES = (VALID_INNATE_STATUSES |
                            0x1402100000)
    BENEFICIAL_STATUSES =   0xc278600000
    RERAISE_STATUS =        0x0000200000
    FAITH_STATUS =          0x8000000000
    INNOCENT_STATUS =       0x4000000000
    INVITE_STATUS =         0x0000004000
    FLOAT_STATUS =          0x0000400000

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
        'Beowulf', 'Cloud', 'Reis',
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
    def random_degree(self):
        return JobStatsObject.random_degree

    @clached_property
    def character_jobs(self):
        from collections import OrderedDict

        character_jobs = defaultdict(set)
        for u in UnitObject.every:
            if u.entd_index >= 0x1db:
                continue
            if u.has_unique_name:
                character_jobs[u.character_name].add(u.old_data['job_index'])

        JobObject._character_jobs = OrderedDict()
        for name in character_jobs:
            JobObject._character_jobs[name] = [
                JobObject.get(j) for j in sorted(character_jobs[name])
                if JobObject.get(j).is_special]

        return JobObject._character_jobs

    @property
    def profile(self):
        if not self.is_generic:
            raise NotImplementedError

        generics = [j for j in JobObject.every if j.is_generic]
        assert self in generics

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
        if self.character_name in ['NONE', 'RANDOM GENERIC']:
            return [self]
        relatives = [j for j in JobObject.every
                     if j.character_name == self.character_name]
        relatives = sorted(relatives, key=lambda r: r.signature)
        return relatives

    @cached_property
    def canonical_relative(self):
        if self.character_name in ['NONE', 'RANDOM GENERIC']:
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
            if random.random() > random_degree:
                continue
            value = getattr(self, attr)
            mask = (1 << random.randint(0, 39))
            if mask & self.VALID_START_STATUSES:
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
                    self.innates[i] = other
                else:
                    self.innates[i] = (
                        random.choice(AbilityObject.passive_pool).index)

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
                random_difficulty = self.random_difficulty ** 0.5
            else:
                random_difficulty = self.random_difficulty

            if not isinstance(attrs, tuple):
                attrs = (attrs,)
            for attr in attrs:
                value = getattr(self, attr)
                ratio = sum([random.random() for _ in range(3)]) / 3
                if attr.endswith('growth'):
                    boost = value / (random_difficulty ** factor)
                elif attr.endswith('mult'):
                    boost = value * (random_difficulty ** factor)
                value = (value * ratio) + (boost * (1-ratio))
                value = max(0, min(0xff, value))
                setattr(self, attr, int(round(value)))

    def mutate(self):
        super().mutate()
        if self.is_lucavi:
            self.boost_stats(self.LUCAVI_FACTOR)
        elif not (self.is_generic or self.is_recruitable):
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
            ratio = 2 * index / max_index
            assert 0 <= ratio <= 2

            multiplier = (self.random_difficulty ** 0.5) - 1
            if ratio > 1:
                multiplier = 1 + (multiplier * (ratio-1))
            elif ratio < 1:
                multiplier = 1 - (multiplier * (1-ratio))
            for attrs in self.randomselect_attributes:
                if isinstance(attrs, tuple):
                    for attr in attrs:
                        variance = sum(random.random() for _ in range(3)) / 3
                        mult = (multiplier * variance) + (1 - variance)
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


class WeaponStatusObject(TableObject):
    flag = 'y'
    custom_random_enable = flag

    def mutate(self):
        if random.choice([True, False]):
            WeaponObject.get(self.index).mutate_status()
            WeaponObject.get(self.index).mutate_proc()
        else:
            WeaponObject.get(self.index).mutate_proc()
            WeaponObject.get(self.index).mutate_status()


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

    BANNED_SKILLS = set([0x28, 0x2d, 0xdb, 0xdc] + lange(0x165, 0x16f))
    MATH_SKILLSETS = {0xa, 0xb, 0xc, 0x10}
    MATH = 0x15
    CHAOS = 0x7c
    BANNED_ANYTHING = {0x18}  # mimic
    BANNED_SKILLSET_SHUFFLE = {0, 1, 2, 3, 6, 8, 0x11, 0x12, 0x13, 0x14, 0x15,
                               0x18, 0x34, 0x38, 0x39, 0x3b, 0x3e, 0x9c, 0xa1
                               } | BANNED_ANYTHING

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
        return 5 <= self.index <= 0x18

    @cached_property
    def is_altima_secondary(self):
        seconds = [u.old_data['secondary'] for u in ENTDObject.get(0x1b9).units
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
        shuffled_names = list(names)
        random.shuffle(shuffled_names)
        for sending, receiving in zip(names, shuffled_names):
            if sending == receiving:
                continue
            skillsets = character_skillsets[sending]
            best = pick_best_skillset(skillsets)
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

    def cleanup(self):
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
    custom_random_enable = flag

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

    @classmethod
    def randomize_all(self):
        old_ranked = self.ranked
        jp_values = [jro.get_similar().get_jp_total(old=True)
                     for jro in old_ranked]
        max_jp = max(jp_values)
        jp_values = [mutate_normal(jp, 0, max_jp,
                                   random_degree=self.random_degree)
                     for jp in jp_values]
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
                if random.random() > max(self.random_degree ** 2.5, 0.01):
                    temp = [c for c in candidates if c in my_pool]
                    if temp:
                        candidates = temp

                max_index = len(candidates)-1
                index = int(round(
                    (random.random() ** (self.random_degree ** 0.5))
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

        super().randomize_all()

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
                and self.entd_index == 0x1cc):
            assert all(e.map_index == 0x32 for e in self.encounters)
            self.map_index = 0x32
            self.old_data['map_index'] = 0x32


class EncounterObject(TableObject):
    flag = 'f'
    flag_description = 'enemy and ally formations'
    custom_random_enable = flag

    FIXED_WEATHER_ENTDS = [0x19f, 0x1b5, 0x1c2]
    FIXED_SONGS = {0, 17, 18, 19, 20, 21, 22, 23, 24,
                   27, 28, 29, 30, 31, 32, 33, 35, 40,
                   41, 42, 43, 44, 45, 46, 47, 48, 49, 50,
                   51, 52, 53, 54, 55, 56, 57, 59, 60, 63, 64, 65,
                   69, 70, 71, 72, 73, 74, 75, 79, 98}
    DUMMIED_SONGS = set(range(81, 97)) - FIXED_SONGS
    CANDIDATE_SONGS = set(range(100)) - FIXED_SONGS
    used_music = set()

    GARILAND = 0x9
    ENDING = 0x12b
    ENDING_MUSIC = 0x45

    NO_REPLACE = {0x184, 0x185, 0x1c2}
    MAP_MOVEMENTS_FILENAME = path.join(tblpath, 'map_movements.txt')
    map_movements = defaultdict(list)
    for line in open(MAP_MOVEMENTS_FILENAME):
        map_index, data = line.split()
        map_index = int(map_index, 0x10)
        unit, x, y = data.split(',')
        unit = int(unit, 0x10)
        x, y = int(x), int(y)
        map_movements[map_index].append((unit, x, y))

    REPLACING_MAPS = [
        1, 4, 8, 9, 11, 14, 15, 18, 20, 21, 23, 24, 26, 37, 38,
        41, 43, 46, 48, 51, 53, 62, 65, 68, 71, 72, 73, 75,
        76, 92, 93, 95, 96, 97, 98, 99, 100, 101, 102, 104,
        115, 116, 117, 118, 119, 125]
    DONE_MAPS = set()
    REPLACED_MAPS = set()

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
        return 'ENC {0:0>3X} ENTD {1:0>3X} MAP {0:0>3}'.format(
            self.index, self.entd_index, self.old_data['map_index'])

    @property
    def is_replaceable(self):
        if self.entd_index in self.NO_REPLACE:
            return False
        if 'bigtide' in get_activated_codes():
            return (self.num_characters
                        and not hasattr(self.map, '_loaded_from'))
        return (self.num_characters and not self.movements
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

    @property
    def movements(self):
        return {u: (x, y) for (u, x, y) in
                self.map_movements[self.old_data['map_index']]}

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
        for u, (x, y) in self.movements.items():
            self.map.set_occupied(x, y)
        for u in self.units:
            if u.has_unique_name and (u.is_present_old or
                                      u.unit_id in self.movements):
                self.map.set_occupied(u.old_data['x'], u.old_data['y'])
                continue
        if self.movements and 'bigtide' not in get_activated_codes():
            for u in self.units:
                if u.unit_id in self.movements:
                    self.map.set_occupied(u.old_data['x'], u.old_data['y'])
                    continue

    def preprocess(self):
        self.set_occupied()
        if self.index == 0x1b2 and self.formation_indexes == [232, 324]:
            self.formation_indexes = [323, 324]
            self.old_data['formation_indexes'] = self.formation_indexes
            self.clear_cache()

    def is_map_movement_compatible(self, c):
        movement_tiles = set(self.movements.values())
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
        if self.movements:
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

        # do this after creating new units?
        units = list(self.units)
        random.shuffle(units)
        for u in units:
            if (u.unit_id in self.movements
                    and 'bigtide' not in get_activated_codes()):
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

    def preprocess(self):
        f = get_open_file(self.filename)

        index = 0
        instructions = []
        while True:
            f.seek(self.BASE_POINTER + self.instructions_pointer
                   + (2*len(instructions)))
            instruction_pointer = int.from_bytes(f.read(2), byteorder='little')
            if instruction_pointer == 0:
                break
            f.seek(self.BASE_POINTER + instruction_pointer)
            instructions.append(self.get_instruction(f))
            index += 1
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
        custom_names = [line.strip() for line in open(CUSTOM_NAMES_FILEPATH)
                        if line.strip()]
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
    ENDING_SCENES = (0x12c, 0x147)

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
        if text_offset >= 0x1800:
            assert text_offset == 0xf2f2f2f2
        length = min(text_offset, 0x1800) - 4
        event_data = f.read(length)
        length = 0x1800 - (length + 4)
        text_data = f.read(length)

        f.seek(self.pointer + 0x1800)
        value = int.from_bytes(f.read(4), byteorder='little')
        if value != 0xf2f2f2f2:
            self._no_modify = True

        self.old_text_offset = text_offset
        self.instructions = self.data_to_instructions(event_data)
        self.messages = self.data_to_messages(text_data)
        assert self.instruction_data == event_data[:len(self.instruction_data)]
        assert self.message_data == text_data[:len(self.message_data)]
        if self.message_indexes and text_offset >= 0x1800:
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
        if 'automash_dialogue.txt' in get_activated_patches():
            self.automash()

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
            if rider.unit_id == 0xff:
                rider.unit_id = next_unit_id
                next_unit_id += 1
            elevation = 1 if mount.is_upper else 0
            instruction = (0x28, (rider.unit_id, 0x00, mount.x, mount.y,
                                  elevation, 0x00, 0x7f, 0x01))
            mount_instructions.append(instruction)
        assert self.instructions[-1] == (0xdb, [])
        self.instructions = (self.instructions[:-1] + mount_instructions
                             + [self.instructions[-1]])
        assert self.instructions[-1] == (0xdb, [])

    def cleanup(self):
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
        f = get_open_file(self.filename)
        f.write(self.data)


class GNSObject(MapMixin):
    flag = 'm'
    flag_description = 'custom maps'
    custom_random_enable = flag

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

    if not CUSTOM_INDEX_OPTIONS:
        print('WARNING: No custom maps found.')

    WARJILIS = 42
    ZARGHIDAS = 33

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

    def cleanup(self):
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

    USED_MAPS = lange(0, 0x14b) + lange(0x180, 0x1d6)

    MONSTER_GRAPHIC = 0x82
    MALE_GRAPHIC = 0x80
    FEMALE_GRAPHIC = 0x81
    GENERIC_GRAPHICS = (MALE_GRAPHIC, FEMALE_GRAPHIC)
    CHOCOBO_SPRITE_ID = (0x82, 0x86)
    NO_JOB_CHANGE = {0x91}

    ORBONNE_OPENING_ENTD = 0x183

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
    def is_human(self):
        return (self.graphic != self.MONSTER_GRAPHIC
                and not self.job.is_lucavi)

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
            u._human_unit_pool_member = self

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
                and u.get_gender() is not None]
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
                    jp = jp * self.random_difficulty
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
        assert not self.map.get_occupied(x, y)
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

        max_index = len(tiles)-1
        factor = 1 - (random.random() ** (1 / (random_degree ** 0.7)))
        assert 0 <= factor <= 1
        index = int(round(max_index * factor))
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
                test = random.choice(available_sprites)
            if (isinstance(test, UnitObject)
                    and random.random() > self.random_degree ** 0.5):
                continue
            break

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
                if equip == 'righthand':
                    candidates = [c for c in candidates if c.get_bit('weapon')]
                elif equip == 'lefthand':
                    dual_wield = False
                    if 1 <= template.old_data['lefthand'] <= 0xfd:
                        tleft = ItemObject.get(template.old_data['lefthand'])
                        if tleft.get_bit('weapon'):
                            dual_wield = True
                    if not dual_wield:
                        candidates = [c for c in candidates
                                      if c.get_bit('shield')]
                else:
                    candidates = [c for c in candidates if c.get_bit(equip)]

            if random.random() > self.random_degree ** 2:
                candidates = [c for c in candidates if self.job.can_equip(c)]

            if equip == 'righthand' and self.requires_sword:
                swords = [c for c in candidates if c.is_sword]
                if (len(swords) == 0
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

    def attempt_chocobo_knight(self):
        if hasattr(self, '_chocobo_rider'):
            return

        candidates = [u for u in self.neighbors if u.is_human
                      and u.allegiance == self.allegiance
                      #and u.unit_id >= 0x80
                      and (u.unit_id < 0xff or u.is_present)
                      and u.is_standing_on_solid_ground
                      and not hasattr(u, '_chocobo_mount')]
        if candidates:
            chosen = random.choice(candidates)
            chosen._chocobo_mount = self
            self._chocobo_rider = chosen
            self.x = chosen.x
            self.y = chosen.y
            self.relocate_nearest_good_tile()

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
                and self.encounter.num_characters > 0):
            self.attempt_chocobo_knight()

        if self.is_important and self.map is not None:
            badness = self.map.get_tile_attribute(
                self.x, self.y, 'bad_regardless',
                upper=self.is_upper, singleton=True)
            try:
                assert badness is not True
                if badness is not False:
                    assert (self.x == self.old_data['x'] and
                            self.y == self.old_data['y'] and
                            self.map == self.old_map and False in badness
                            and not hasattr(self.map, '_loaded_from'))
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
            self.normalize_level(boost)

        if (self.entd_index in ENTDObject.NERF_ENTDS
                and self.get_bit('enemy_team')):
            self.level = min(self.level, self.old_data['level'])
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
            if random.random() < (self.random_degree ** 0.65) / 2:
                self.set_bit('join_after_event', True)

        if self.job.character_name == 'Ramza':
            self.set_bit('join_after_event',
                         self.get_bit('join_after_event', old=True))

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

        if self.is_important and self.encounter is not None:
            assert 0 <= self.x < self.map.width
            assert 0 <= self.y < self.map.length

        assert (0 <= self.unlocked <=
                JobObject.MIME_INDEX - JobObject.SQUIRE_INDEX)

        if (self.character_name == 'Alma'
                and self.graphic == self.old_data['graphic']):
            altima = [u for u in ENTDObject.get(0x1b9).units
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

        if (self.entd_index == self.ORBONNE_OPENING_ENTD
                and not self.get_bit('enemy_team')):
            self.set_bit('control', True)

        if self.job.is_lucavi and self.is_valid and not self.job.is_altima:
            if UnitObject.flag in get_flags():
                assert 1 <= self.secondary <= 0xfd
            else:
                assert self.secondary == self.old_data['secondary']
            if not SkillsetObject.get(self.secondary).is_lucavi_appropriate:
                self.secondary = 0

        if not self.is_canonical:
            for attr in ['brave', 'faith', 'month', 'day']:
                setattr(self, attr, getattr(self.canonical_relative, attr))

        if (self.unit_id > 0 and self.encounter
                and self.unit_id in self.encounter.movements):
            self.set_bit('always_present',
                         self.get_bit('always_present', old=True))
            self.set_bit('randomly_present',
                         self.get_bit('randomly_present', old=True))

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

    VALID_INDEXES = (
        lange(1, 9) + lange(0xd, 0x21) + lange(0x25, 0x2d) +
        lange(0x31, 0x45) + lange(0x49, 0x51) + lange(0x52, 0xfd) +
        lange(0x180, 0x1d6))
    NAMED_GENERICS = {}

    DEEP_DUNGEON = set(
            [0x192] +
            lange(0xb1, 0xb5) + lange(0xc9, 0xcd) +
            lange(0xd5, 0xd9) + lange(0xe1, 0xfd))
    LUCAVI_ENTDS = {0x1a0, 0x1b0, 0x1b9, 0x1c9, 0x1cb}
    SPECIAL_CASE_SPRITES = LUCAVI_ENTDS | DEEP_DUNGEON
    WIEGRAF = {0x190, 0x1a8, 0x1b0}
    VELIUS = 0x1b0

    FINAL_BATTLE = 0x1b9
    CEMETARY = 0x134

    NERF_ENTDS = {0x183, 0x184, 0x185}

    @classproperty
    def after_order(self):
        return [JobReqObject]

    @classmethod
    def get_unused(self):
        unused = sorted(set(range(0x100, 0x200)) -
                        {enc.entd_index for enc in EncounterObject.every})
        unused = [ENTDObject.get(i) for i in unused]
        unused = [e for e in unused if not e.is_valid]
        return unused[-1]

    @cached_property
    def units(self):
        return [UnitObject.get((self.index << 4) | i) for i in range(0x10)]

    @cached_property
    def avg_level(self):
        levels = [u.old_data['level'] for u in self.units
                  if u.is_present_old and 1 <= u.old_data['level'] <= 99
                  and not u.is_ally]
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
                new_sprite = u.get_similar_sprite(exclude_sprites=new_sprites,
                                                  random_degree=1.0)
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
    def cleanup(self):
        if DEBUG:
            self.colors[TEST_PALETTE_INDEX] = 0x7c1f

class SpritePaletteObject(TableObject):
    def cleanup(self):
        if DEBUG:
            self.colors[TEST_PALETTE_INDEX] = 0x7c1f


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
    load_event_patch(path.join(tblpath, 'patch_fur_shop_from_start.txt'))
    load_event_patch(
        path.join(tblpath, 'patch_propositions_from_start.txt'))
    load_event_patch(
        path.join(tblpath, 'patch_battle_conditionals_base.txt'))
    replace_ending()

    if 'murond_exit_patch.txt' in get_activated_patches():
        load_event_patch(path.join(tblpath, 'patch_gauntlet.txt'))

    add_bonus_battles()


def write_spoiler():
    spoiler_filename = '%s.txt' % get_seed()
    f = open(spoiler_filename, 'w+')
    f.write(JobReqObject.jobtree + '\n\n')
    generics = sorted([j for j in JobObject.every if j.is_generic],
                      key=lambda j: j.name)

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
            }
        run_interface(ALL_OBJECTS, snes=False, codes=codes,
                      custom_degree=True, custom_difficulty=True)

        for code in sorted(codes):
            if code in get_activated_codes():
                print('%s code activated!' % code.upper())

        xml_directory, xml_config = path.split(XML_PATCH_CONFIG_FILEPATH)
        xml_patches = xml_patch_parser.get_patches(xml_directory, xml_config)
        for p in xml_patches:
            xml_patch_parser.patch_patch(SANDBOX_PATH, p)

        handle_patches()

        clean_and_write(ALL_OBJECTS)

        for p in xml_patches:
            xml_patch_parser.patch_patch(SANDBOX_PATH, p, verify=True)

        write_spoiler()
        write_cue_file()
        finish_interface()

    except Exception:
        print(format_exc())
        input('Press Enter to close this program. ')
