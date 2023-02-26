import json
import re

with open("data/tactics.json", "r") as f:
    TACTICS = json.load(f)
with open("data/worlds.json", "r") as f:
    WORLDS = json.load(f)["worlds"]

_LEVEL_DATA_SEPARATION_MARKER = re.compile(r"\(\*\s*Level\s+(\d+)\s+(.*?)\s*\*\)")
_LEVEL_DATA = re.compile(r"\(\*\s*(\w+)\s+(.*?)\s*\*\)")


def _check_int(s):
    if s and s[0] in ('-', '+'):
        return s[1:] and s[1:].isdigit()
    return s.isdigit()


def _validate_level(level, name):
    if "lemma" not in level:
        raise AttributeError(f"Missing lemma in {name}")

    # add (optional) prologue and epilogue sections,
    # and fix formatting.
    for section in ["prologue", "epilogue"]:
        level[section] = level.get(section, "").strip("(*) \n")


def _parse_world_file(world, f):
    assert not world["levels"]

    # only necessary lines, and level markers
    reduced_world_file = []

    current = 0
    state = None
    level = {}
    while line := f.readline():
        line = line.strip()

        # check if we are going to read a new section
        match = re.match(_LEVEL_DATA_SEPARATION_MARKER, line)
        if match is not None:
            level_no, section = match.groups()
            level_no = int(level_no)
            if level_no != current:
                raise ValueError(f"Unexpected level number, expected {current}, got {level_no}")

            if section == "end":
                level["level"] = current
                _validate_level(level, f"level {current} in world {world['world']}")
                world["levels"].append(level)

                # reset data
                level = {}
                state = None
                current += 1
            else:
                state = section
        # check section based on state
        elif state == "data":
            # parse level data
            match = re.match(_LEVEL_DATA, line)
            if match is None:
                continue

            key, value = match.groups()
            value = value.strip()
            # json like data
            if value == "null":
                value = None
            elif _check_int(value):
                value = int(value)
            level[key] = value
        elif state == "prologue" or state == "epilogue" or state == "proof":
            # multiline attributes
            if state not in level:
                if state == "proof":
                    # proof start for level, insert level marker
                    reduced_world_file.append(current)
                level[state] = ""
            level[state] += f"{line}\n"

            if state == "proof":
                reduced_world_file.append(line)

        elif state == "lemma":
            # level main lemma, there must be precisely one of these
            if line:
                if "lemma" in level:
                    raise ValueError(f"Double lemma for level {current} in world {world['world']}:"
                                     f"Have: {level['lemma']}\nGot: {level['lemma']}")
                level["lemma"] = line
                reduced_world_file.append(line)
        elif state is None:
            reduced_world_file.append(line)
        else:
            raise ValueError(f"Invalid state {state} for level {current} in world {world['world']}")

    if level or (state is not None):
        raise EOFError(f"Unexpected end of file while parsing world {world['world']}")
    world["reduced_file"] = reduced_world_file


for i, world in enumerate(WORLDS):
    world["world"] = i
    world["levels"] = []
    with open(f"coq/{world['file']}", "r") as f:
        _parse_world_file(world, f)


def get_level(world, level):
    if world >= len(WORLDS):
        raise IndexError(f"Could not find world with index {world}")
    _world = WORLDS[world]
    if level >= len(_world["levels"]):
        raise IndexError(f"Could not find level with index {level} in world {_world['name']}")
    _level = _world["levels"][level]

    return _world, _level


def get_tactics(world, level):
    tactics = []
    # only tactics up to the one marked in level
    if level["tactics"] is not None:
        for t in TACTICS["tactics"]:
            tactics.append(t)
            if t["name"] == level["tactics"]:
                break
    return tactics


def get_theorems(world, level):
    theorems = []
    if level["theorems"] is not None:
        for w in TACTICS["theorems"]:
            # all previous worlds
            if w["world"] < world["world"]:
                theorems.append(w)
            # only theorem up to the one marked in level
            elif w["world"] == world["world"]:
                _w = dict(w)
                _w["theorems"] = []
                for t in w["theorems"]:
                    _w["theorems"].append(t)
                    if t["name"] == level["theorems"]:
                        break
                theorems.append(_w)
    return theorems


if __name__ == '__main__':
    from pprint import pprint
    pprint(WORLDS)