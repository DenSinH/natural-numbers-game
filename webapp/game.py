import json


with open("data/tactics.json", "r") as f:
    TACTICS = json.load(f)
with open("data/worlds.json", "r") as f:
    WORLDS = json.load(f)["worlds"]


def get_level(world, level):
    if world > len(WORLDS):
        raise exceptions.NotFound(f"Could not find world with index {world}")
    _world = WORLDS[world]
    if level > len(_world["levels"]):
        raise exceptions.NotFound(f"Could not find level with index {level} in world {world['name']}")
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
            elif w["world"] == world:
                _w = dict(w)
                _w["theorems"] = []
                for t in w["theorems"]:
                    _w["theorems"].append(t)
                    if t["name"] == level["theorems"]:
                        break
                theorems.append(_w)
    return theorems