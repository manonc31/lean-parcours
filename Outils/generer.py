#!/usr/bin/env python3
"""
Générateur du parcours (outil de maintenance — tu n'as pas besoin de le lancer).

Source de vérité : les fichiers `Solutions/**/*.lean`. Chacun commence par un bloc

    /- @parcours
    titre: Commutativité de l'addition
    difficulte: 2
    genre: exo            (exo | pont | boss | ouvert | cours)
    debloque: Nat         (jetons débloqués pour les exercices qui en dépendent)
    interdit: Classical.em, Classical.propDecidable
    permis: Nat.gcd*       (exceptions de bibliothèque propres à l'exercice)
    solution: non         (pour un boss sans solution de référence)
    indice: premier indice
    indice: deuxième indice
    -/

et les preuves à faire sont marquées par `-- @exo` sur la ligne du `:=`.

Sorties :
  * `Exercices/**/*.lean` — les exercices (preuves remplacées par `sorry`)
      (un fichier existant n'est réécrit que s'il est encore vierge, ou avec --force)
  * `.parcours/vierges/`   — copies d'origine (pour `./parcours reset`)
  * `.parcours/graphe.json` et `.parcours/verif.json`
"""
import json
import os
import re
import sys

RACINE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SOL = os.path.join(RACINE, "Solutions")
PAR = os.path.join(RACINE, "Exercices")
DATA = os.path.join(RACINE, ".parcours")
VIERGES = os.path.join(DATA, "vierges")

DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|nonrec|unsafe)\s+)*"
    r"(theorem|def|abbrev|instance|structure|inductive|example)\s+([^\s:({\[]+)?"
)


def etoiles(n):
    return "★" * n + "☆" * (5 - n)


def lire_meta(lignes):
    """Extrait le bloc /- @parcours ... -/ ; renvoie (meta, lignes_restantes)."""
    meta = {"indices": []}
    if not lignes or not lignes[0].startswith("/- @parcours"):
        raise ValueError("bloc /- @parcours manquant en tête de fichier")
    i = 1
    while i < len(lignes) and lignes[i].strip() != "-/":
        l = lignes[i]
        if l.strip():
            k, _, v = l.partition(":")
            k, v = k.strip(), v.strip()
            if k == "indice":
                meta["indices"].append(v)
            else:
                meta[k] = v
        i += 1
    i += 1
    while i < len(lignes) and lignes[i].strip() == "":
        i += 1
    return meta, lignes[i:]


def liste(v):
    return [x.strip() for x in v.split(",") if x.strip()] if v else []


def transformer(lignes, ident, meta):
    """Produit le texte de l'exercice et la liste des cibles."""
    sortie = []
    cibles = []
    pile = []  # (genre, nom)
    enonce = None
    i = 0
    n = len(lignes)
    dans_doc = False
    doc = []
    doc_fait = False
    while i < n:
        l = lignes[i]
        s = l.strip()
        # imports
        if s.startswith("import Solutions."):
            sortie.append(l.replace("import Solutions.", "import Exercices.", 1))
            i += 1
            continue
        # bloc de documentation principal
        if not doc_fait and s.startswith("/-!"):
            dans_doc = True
            doc = [l]
            if s.endswith("-/") and len(s) > 4:
                dans_doc = False
            i += 1
            if dans_doc:
                while i < n:
                    doc.append(lignes[i])
                    if lignes[i].strip().endswith("-/"):
                        break
                    i += 1
                i += 1
            texte = "\n".join(doc)
            corps = texte.strip()[3:]
            corps = corps[: corps.rfind("-/")].strip("\n")
            enonce = corps.strip()
            pied = (
                "\n\n---\n"
                f"*Exercice* `{ident}` · difficulté {etoiles(int(meta.get('difficulte', 1)))}"
            )
            if meta.get("genre") != "cours":
                pied += (
                    "\n\n💡 Indices : `./parcours indice "
                    + ident
                    + "` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier "
                    "(dans l'infoview), ou lance `./parcours verifier`."
                )
            sortie.append("/-!\n" + corps.rstrip() + pied + "\n-/")
            doc_fait = True
            continue
        # namespaces / sections
        m = re.match(r"^(namespace|section|mutual)\b\s*(\S*)", l)
        if m:
            pile.append((m.group(1), m.group(2)))
        m = re.match(r"^end\b\s*(\S*)", l)
        if m and pile:
            pile.pop()
        # preuve à remplacer
        if "-- @exo" in l:
            code = l[: l.index("-- @exo")].rstrip()
            # retrouver la déclaration
            j = i
            while j >= 0 and not DECL_RE.match(lignes[j]):
                j -= 1
            if j < 0:
                raise ValueError(f"{ident}: impossible de trouver la déclaration de la ligne {i+1}")
            dm = DECL_RE.match(lignes[j])
            genre, nom = dm.group(1), dm.group(2)
            prefixe = ".".join(x[1] for x in pile if x[0] == "namespace" and x[1])
            nom_complet = (prefixe + "." + nom) if prefixe else nom
            cibles.append(nom_complet)
            est_def = genre in ("def", "abbrev", "instance")
            if code.endswith(" where"):
                code = code[: -len(" where")] + " :="
            if ":=" in code:
                avant = code[: code.rindex(":=")].rstrip()
                if est_def:
                    nouveau = avant + " :=\n  sorry"
                else:
                    nouveau = avant + " := by\n  sorry"
            else:
                nouveau = code + " :=\n  sorry"
            sortie.append(nouveau)
            i += 1
            debut = i
            while i < n and (lignes[i].strip() == "" or lignes[i][0] in " \t"):
                i += 1
            # garder les lignes vides finales
            k = i
            while k > debut and lignes[k - 1].strip() == "":
                k -= 1
            sortie.extend([""] * (i - k))
            continue
        sortie.append(l)
        i += 1
    if enonce is None:
        raise ValueError(f"{ident}: bloc /-! … -/ (énoncé) manquant")
    return "\n".join(sortie).rstrip() + "\n", cibles, enonce


def main():
    force = "--force" in sys.argv
    with open(os.path.join(RACINE, "Outils", "branches.json"), encoding="utf-8") as f:
        branches = json.load(f)
    with open(os.path.join(RACINE, "Outils", "regles.json"), encoding="utf-8") as f:
        regles = json.load(f)
    hashes = {}
    hp = os.path.join(DATA, "hashes.json")
    if os.path.exists(hp):
        with open(hp, encoding="utf-8") as f:
            for h in json.load(f):
                hashes[h["cible"]] = h["hash"]

    exos = {}
    for dossier, _, fichiers in os.walk(SOL):
        for fn in sorted(fichiers):
            if not fn.endswith(".lean"):
                continue
            chemin = os.path.join(dossier, fn)
            rel = os.path.relpath(chemin, SOL)
            ident = rel[:-5].replace(os.sep, ".")
            with open(chemin, encoding="utf-8") as f:
                texte = f.read()
            lignes = texte.split("\n")
            try:
                meta, reste = lire_meta(lignes)
                exo_txt, cibles, enonce = transformer(reste, ident, meta)
            except ValueError as e:
                print("ERREUR", rel, e)
                sys.exit(1)
            importe = [
                m.group(1)
                for m in re.finditer(r"^import Solutions\.(\S+)", texte, re.M)
            ]
            deps = importe + [d for d in liste(meta.get("requiert", "")) if d not in importe]
            genre = meta.get("genre", "exo")
            if genre != "cours" and not cibles:
                print("ERREUR", rel, ": aucune cible (-- @exo)")
                sys.exit(1)
            if genre != "cours" and "#verifier" not in texte:
                print("ATTENTION", rel, ": pas de #verifier")
            sans_sol = meta.get("solution", "oui") == "non" or genre == "ouvert"
            exos[ident] = {
                "id": ident,
                "titre": meta.get("titre", ident),
                "branche": ident.split(".")[0],
                "difficulte": int(meta.get("difficulte", 1)),
                "genre": genre,
                "fichier": "Exercices/" + rel.replace(os.sep, "/"),
                "solution": "" if sans_sol or genre == "cours" else "Solutions/" + rel.replace(os.sep, "/"),
                "deps": deps,
                "importe": importe,
                "debloque": liste(meta.get("debloque", "")),
                "interdit": liste(meta.get("interdit", "")),
                "permis": liste(meta.get("permis", "")),
                "enonce": enonce,
                "indices": meta["indices"],
                "celebre": int(meta.get("celebre", 0)),
                "cibles": cibles,
                "_texte": exo_txt,
            }

    # vérifications du graphe
    for e in exos.values():
        for d in e["deps"]:
            if d not in exos:
                print("ERREUR", e["id"], ": dépendance inconnue", d)
                sys.exit(1)
        if e["branche"] not in [b["id"] for b in branches]:
            print("ERREUR", e["id"], ": branche inconnue", e["branche"])
            sys.exit(1)
    jetons = {j["nom"] for j in regles["jetons"]}
    for e in exos.values():
        for j in e["debloque"]:
            if j not in jetons:
                print("ERREUR", e["id"], ": jeton inconnu", j)
                sys.exit(1)

    # fermeture transitive des dépendances
    def fermeture(cle):
        memo = {}

        def ancetres(i, pile=()):
            if i in memo:
                return memo[i]
            if i in pile:
                print("ERREUR : cycle de dépendances via", i)
                sys.exit(1)
            r = set()
            for d in exos[i][cle]:
                r.add(d)
                r |= ancetres(d, pile + (i,))
            memo[i] = r
            return r
        return ancetres

    anc_deps = fermeture("deps")
    anc_imports = fermeture("importe")
    for e in exos.values():
        auto = []
        # un déblocage n'est vérifiable que si le pont est importé (transitivement)
        for a in sorted(anc_imports(e["id"])):
            for j in exos[a]["debloque"]:
                auto.append({"jeton": j, "par": a})
        e["autorise"] = auto
        for a in sorted(anc_deps(e["id"]) - anc_imports(e["id"])):
            if exos[a]["debloque"]:
                print("ATTENTION", e["id"], ": dépend de", a, "(qui débloque", exos[a]["debloque"], ") sans l'importer")

    # écriture des fichiers d'exercices
    os.makedirs(DATA, exist_ok=True)
    nb_ecrits = nb_gardes = 0
    for e in exos.values():
        dest = os.path.join(RACINE, e["fichier"])
        vierge = os.path.join(VIERGES, e["fichier"])
        ancien_vierge = None
        if os.path.exists(vierge):
            with open(vierge, encoding="utf-8") as f:
                ancien_vierge = f.read()
        os.makedirs(os.path.dirname(vierge), exist_ok=True)
        with open(vierge, "w", encoding="utf-8") as f:
            f.write(e["_texte"])
        ecrire = force or not os.path.exists(dest)
        if not ecrire:
            with open(dest, encoding="utf-8") as f:
                actuel = f.read()
            ecrire = actuel == ancien_vierge or actuel == e["_texte"]
        if ecrire:
            os.makedirs(os.path.dirname(dest), exist_ok=True)
            with open(dest, "w", encoding="utf-8") as f:
                f.write(e["_texte"])
            nb_ecrits += 1
        else:
            nb_gardes += 1

    ordre = sorted(exos.values(), key=lambda e: e["id"])
    graphe = {
        "branches": branches,
        "exercices": [
            {k: e[k] for k in ("id", "titre", "branche", "difficulte", "genre", "fichier",
                               "solution", "deps", "importe", "debloque", "enonce", "indices", "celebre")}
            for e in ordre
        ],
    }
    verif = {
        "base": regles["base"],
        "jetons": regles["jetons"],
        "exercices": [
            {
                "id": e["id"],
                "titre": e["titre"],
                "fichier": e["fichier"],
                "cibles": e["cibles"],
                "hashes": [{"cible": c, "hash": hashes[c]} for c in e["cibles"] if c in hashes],
                "autorise": e["autorise"],
                "interdit": e["interdit"],
                "permis": e["permis"],
                "debloque": e["debloque"],
            }
            for e in ordre
        ],
    }
    with open(os.path.join(DATA, "graphe.json"), "w", encoding="utf-8") as f:
        json.dump(graphe, f, ensure_ascii=False, indent=1)
    with open(os.path.join(DATA, "verif.json"), "w", encoding="utf-8") as f:
        json.dump(verif, f, ensure_ascii=False, indent=1)
    sans_hash = sum(1 for e in exos.values() for c in e["cibles"] if c not in hashes)
    print(
        f"{len(exos)} fichiers ({sum(1 for e in exos.values() if e['genre'] != 'cours')} exercices), "
        f"{nb_ecrits} écrits, {nb_gardes} conservés (modifiés par toi), {sans_hash} cibles sans hash."
    )


if __name__ == "__main__":
    main()
