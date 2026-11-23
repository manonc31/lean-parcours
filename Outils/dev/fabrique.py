#!/usr/bin/env python3
"""Fabrique d'exercices (outil de maintenance) : écrit des fichiers Solutions/<Branche>/<Id>.lean
à partir de descriptions compactes. Usage : dans un script de lot,
    from fabrique import exo, ecrire_tout
    exo("Olympiades", "Sept", titre=..., ...)
    ecrire_tout()
puis relancer Outils/generer.py."""
import os

RACINE = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
_EXOS = []


def exo(branche, ident, titre, diff, imports, texte, code, indices, ns, requiert="", genre="",
        celebre=0, solution=True, ressources=()):
    _EXOS.append(dict(branche=branche, ident=ident, titre=titre, diff=diff, imports=imports,
                      texte=texte, code=code, indices=indices, ns=ns, requiert=requiert,
                      genre=genre, celebre=celebre, solution=solution, ressources=ressources))


def _texte(e):
    l = ["/- @parcours", f"titre: {e['titre']}", f"difficulte: {e['diff']}"]
    if e["genre"]:
        l.append(f"genre: {e['genre']}")
    if not e["solution"]:
        l.append("solution: non")
    if e["celebre"]:
        l.append(f"celebre: {e['celebre']}")
    if e["requiert"]:
        l.append(f"requiert: {e['requiert']}")
    for i in e["indices"]:
        l.append(f"indice: {i}")
    l.append("-/")
    for imp in e["imports"]:
        l.append(f"import {imp}")
    l += ["", "/-!", f"# {e['titre']}", "", e["texte"].strip()]
    if e["ressources"]:
        l += ["", "## Ressources"] + [f"- {r}" for r in e["ressources"]]
    l += ["-/", "", f"namespace {e['ns']}", "", e["code"].strip(), "", f"end {e['ns']}", "", "#verifier", ""]
    return "\n".join(l)


def ecrire_tout():
    for e in _EXOS:
        d = os.path.join(RACINE, "Solutions", e["branche"])
        os.makedirs(d, exist_ok=True)
        with open(os.path.join(d, e["ident"] + ".lean"), "w", encoding="utf-8") as f:
            f.write(_texte(e))
    print(len(_EXOS), "fichiers écrits.")
