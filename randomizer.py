from randomtools.tablereader import (
    TableObject, addresses, get_activated_patches, get_open_file,
    mutate_normal, get_seed, get_global_label, tblpath,
    get_random_degree, get_difficulty, write_patch)
from randomtools.utils import (
    classproperty, cached_property, utilrandom as random)
from randomtools.interface import (
    run_interface, clean_and_write, finish_interface,
    get_activated_codes, get_flags, get_outfile,
    write_cue_file)
from collections import Counter, defaultdict
from math import ceil
from os import path
from sys import argv
from traceback import format_exc


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
    STORYLINE_RECRUITABLE_JOBS = [0xd, 0xf, 0x16, 0x1a, 0x1e, 0x1f,
                                  0x29, 0x2a, 0x32, 0x90, 0x91]

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

    @property
    def is_generic(self):
        return 0x4a <= self.index <= 0x5d

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
    BANNED_SKILLSET_SHUFFLE = [0, 1, 2, 3, 6, 8, 0x11, 0x12, 0x13, 0x14, 0x15,
                               0x18, 0x34, 0x38, 0x39, 0x3b, 0x3e, 0x9c, 0xa1]
    MATH_SKILLETS = [0xa, 0xb, 0xc, 0x10]
    BANNED_ANYTHING = [0x18]

    @property
    def is_generic(self):
        return 5 <= self.index <= 0x18


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
class MoveFindObject(TableObject): pass
class FormationObject(TableObject): pass
class EncounterObject(TableObject): pass


class UnitObject(TableObject):
    DAYS_IN_MONTH = {1: 31, 2: 28, 3: 31, 4: 30, 5: 31, 6: 30,
                     7: 31, 8: 31, 9: 30, 10: 31, 11: 30, 12: 31}

    USED_MAPS = lange(0, 0x14b) + lange(0x180, 0x1d6)
    FIXED_WEATHER = [0x19f, 0x1b5, 0x1c2]

    @property
    def map_id(self):
        return self.index >> 4


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
            }
        run_interface(ALL_OBJECTS, snes=False, codes=codes,
                      custom_degree=True, custom_difficulty=True)

        clean_and_write(ALL_OBJECTS)

        write_cue_file()
        finish_interface()

    except Exception:
        print(format_exc())
        input('Press Enter to close this program. ')
