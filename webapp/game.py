import json
import re

with open("data/tactics.json", "r") as f:
    TACTICS = json.load(f)
with open("data/worlds.json", "r") as f:
    WORLDS = json.load(f)["worlds"]

_LEVEL_DATA_SEPARATION_MARKER = re.compile(r"\(\*\s*Level\s+(\d+\s+)?(.*?)\s*\*\)")
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
    
    # add available argument
    level["available"] = level.get("available", True)
    level["theorems"]  = level.get("theorems", None)

def _parse_world_file(world, f):
    assert not world["levels"]

    # only necessary lines, and level markers
    reduced_world_file = []

    current = 0
    state = None
    level = {}
    while line := f.readline():
        line = line.strip()

        if state is not None:
            if line == "Proof.":
                # level marker
                reduced_world_file.append(current)
                reduced_world_file.append(line)
                state = "proof"
                continue
            elif any(line.startswith(thm) for thm in ["Example", "Lemma", "Fact", "Theorem"]):
                state = "lemma"
                level["lemma"] = line
                reduced_world_file.append(line)
                continue

        # check if we are going to read a new section
        match = re.match(_LEVEL_DATA_SEPARATION_MARKER, line)
        if match is not None:
            level_no, section = match.groups()
            level_no = int(level_no or current)
            if level_no != current:
                raise ValueError(f"Unexpected level number, expected {current}, got {level_no} in world {world['world']}")

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
            elif value == "false":
                value = False
            elif value == "true":
                value = True
            level[key] = value
        elif state == "prologue" or state == "epilogue":
            # multiline attributes
            if state not in level:
                level[state] = ""
            level[state] += f"{line}\n"

        elif state == "lemma":
            # level main lemma, there must be precisely one of these
            if line:
                level["lemma"] += f"\n{line}"
                reduced_world_file.append(line)
        elif state == "proof":
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


def get_theorem_name(level):
    return level["lemma"].split(" ")[1]


def get_theorems(world, level):
    theorems = []
    for w in WORLDS:
        world_theorems = {
            "world": w["world"],
            "theorems": []
        }
        if w["world"] < world["world"]:
            # all theorems from previous worlds
            for t in TACTICS["extra_theorems"][w["world"]]:
                world_theorems["theorems"].append(t)
            
            # add all available level theorems
            for l in w["levels"]:
                if l["available"]:
                    world_theorems["theorems"].append({
                        "name": get_theorem_name(l),
                        "statement": l["lemma"],
                        "world": w["world"]
                    })
        elif w["world"] == world["world"]:
            # add extra theorems up to marked one
            if level["theorems"]:
                for t in TACTICS["extra_theorems"][w["world"]]:
                    world_theorems["theorems"].append(t)
                    if t["name"] == level["theorems"]:
                        break

            # add previous available levels
            for l in w["levels"]:
                if l["level"] >= level["level"]:
                    break
                if l["available"]:
                    world_theorems["theorems"].append({
                        "name": get_theorem_name(l),
                        "statement": l["lemma"],
                        "world": w["world"]
                    })
        else:
            continue
        if world_theorems["theorems"]:
            theorems.append(world_theorems)
    return theorems

def get_next_level(world, level):
    last_level = level["level"] == len(world["levels"]) - 1
    if last_level:
        if world["world"] == len(WORLDS) - 1:
            return None
        else:
            return (world["world"] + 1, 0)
    else:
        return (world["world"], level["level"] + 1)


def get_prev_level(world, level):
    first_level = level["level"] == 0
    if first_level:
        if world["world"] == 0:
            return None
        else:
            return (world["world"] - 1, len(WORLDS[world["world"] - 1]["levels"]) - 1)
    else:
        return (world["world"], level["level"] - 1)


if __name__ == '__main__':
    from pprint import pprint
    pprint(WORLDS)