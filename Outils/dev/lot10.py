import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fabrique import exo, ecrire_tout

LP = "Solutions.Listes.Pont"
RD = "Solutions.Recurrence.Definitions"
LB = "Solutions.Logique.Bilan"

R_src = [0, 1, 2, 3, 4, 5, 26, 25, 24, 15, 12, 9, 16, 13, 10, 17, 14, 11, 18, 19, 20, 21, 22, 23, 33, 34, 35, 27, 28, 29, 30, 31, 32, 53, 52, 51, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 6, 7, 8]
U_src = [2, 5, 8, 1, 4, 7, 0, 3, 6, 9, 10, 11, 12, 13, 14, 47, 50, 53, 18, 19, 17, 21, 22, 16, 24, 25, 15, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 20, 23, 26, 45, 46, 44, 48, 49, 43, 51, 52, 42]
def lst(l):
    s = ", ".join(str(x) for x in l)
    # coupe en lignes de 18
    parts = [", ".join(str(x) for x in l[i:i+18]) for i in range(0, len(l), 18)]
    return "[" + ",\n   ".join(parts) + "]"

exo("Algebre", "Rubik", "Le Rubik's cube", 2, [LP, RD],
"""Les mouvements du Rubik's cube forment un **groupe** : on peut les composer, et chacun a un
inverse. Un fait étonnant : si on répète la séquence « R puis U » (tourner la face droite, puis
la face du haut, d'un quart de tour), le cube revient à son état de départ après exactement
**105** répétitions. Et le célèbre « sexy move » `R U R⁻¹ U⁻¹` revient au départ après 6.

Le cube est codé par ses 54 facettes, numérotées de 0 à 53 ; un mouvement est la liste qui dit,
pour chaque case, de quelle case vient la facette qui s'y trouve après le mouvement.

## À prouver
1. `quatre_quarts : R⁴ = identité`
2. `cent_cinq : (RU)¹⁰⁵ = identité`
3. `pas_moins` : `(RU)¹⁵`, `(RU)²¹` et `(RU)³⁵` ne sont pas l'identité. Comme l'ordre de `RU`
   divise 105 = 3 × 5 × 7 (théorème de Lagrange), c'est donc exactement 105.
4. `sexy_move : (R U R⁻¹ U⁻¹)⁶ = identité`""",
"""def appliquer (mvt etat : List Nat) : List Nat := mvt.map (etat.getD · 0)

def mouvementR : List Nat :=
  """ + lst(R_src) + """

def mouvementU : List Nat :=
  """ + lst(U_src) + """

def depart : List Nat := List.range 54

/-- `puissance f n x` applique `n` fois `f`. -/
def puissance (f : List Nat → List Nat) : Nat → List Nat → List Nat
  | 0, x => x
  | n + 1, x => puissance f n (f x)

def RU (e : List Nat) : List Nat := appliquer mouvementU (appliquer mouvementR e)

def sexy (e : List Nat) : List Nat :=
  puissance (appliquer mouvementU) 3 (puissance (appliquer mouvementR) 3 (RU e))

theorem quatre_quarts : puissance (appliquer mouvementR) 4 depart = depart := by -- @exo
  decide

theorem cent_cinq : puissance RU 105 depart = depart := by -- @exo
  decide +kernel

theorem pas_moins : puissance RU 15 depart ≠ depart ∧ puissance RU 21 depart ≠ depart ∧
    puissance RU 35 depart ≠ depart := by -- @exo
  decide +kernel

theorem sexy_move : puissance sexy 6 depart = depart := by -- @exo
  decide +kernel""",
["Ce sont des calculs sur des listes de 54 nombres : `decide +kernel`.", "`R⁻¹ = R³` : c'est pour ça que `sexy` utilise `puissance … 3`."], "Parcours.Algebre", requiert="Algebre.OrdreElement",
ressources=["[Groupe du Rubik's Cube (Wikipédia)](https://fr.wikipedia.org/wiki/Groupe_du_Rubik%27s_Cube)"])

exo("Algebre", "Triangle", "Les symétries du triangle", 1, [LP, RD],
"""Un triangle équilatéral a 6 symétries : 3 rotations (0°, 120°, 240°) et 3 réflexions. Elles
forment le groupe `S₃`, le plus petit groupe **non commutatif** : tourner puis retourner n'est pas
la même chose que retourner puis tourner !

Une symétrie est codée par la liste des images des sommets 0, 1, 2. `r` est la rotation d'un tiers
de tour, `s` la réflexion qui fixe le sommet 0.

## À prouver
1. `r_cube : r³ = id` et `s_carre : s² = id`
2. `non_commutatif : r ∘ s ≠ s ∘ r`
3. `relation : s ∘ r ∘ s = r⁻¹ = r²` (la relation des groupes diédraux)
4. `six` : en composant `r` et `s` de toutes les façons, on obtient exactement 6 symétries.""",
"""def comp (a b : List Nat) : List Nat := b.map (a.getD · 0)

def ident : List Nat := [0, 1, 2]
def r : List Nat := [1, 2, 0]
def s : List Nat := [0, 2, 1]

theorem r_cube : comp r (comp r r) = ident := by -- @exo
  decide

theorem s_carre : comp s s = ident := by -- @exo
  decide

theorem non_commutatif : comp r s ≠ comp s r := by -- @exo
  decide

theorem relation : comp s (comp r s) = comp r r := by -- @exo
  decide

def engendres : List (List Nat) :=
  [ident, r, comp r r, s, comp r s, comp (comp r r) s]

theorem six : engendres.eraseDups.length = 6 ∧
    ∀ a ∈ engendres, ∀ b ∈ engendres, comp a b ∈ engendres := by -- @exo
  decide""",
["Tout se calcule : `decide`.", "`six` dit aussi que les 6 symétries sont **stables** par composition : c'est bien un groupe."], "Parcours.Algebre", requiert="Algebre.Exemples",
ressources=["[Groupe diédral (Wikipédia)](https://fr.wikipedia.org/wiki/Groupe_di%C3%A9dral)"])

NE = "Parcours.Enigmes"
exo("Enigmes", "Taquin", "Le taquin de Sam Loyd", 2, [LP, RD],
"""En 1880, le taquin (15 pièces glissantes dans un cadre 4 × 4) rend l'Amérique folle. Sam Loyd
promet 1000 dollars à qui remettra dans l'ordre une grille où seules les pièces 14 et 15 sont
échangées. Personne ne gagne : c'est **impossible**, pour une raison de parité.

On joue ici sur un petit taquin 2 × 3 (5 pièces et un trou). Il y a `6! = 720` configurations,
mais seule la **moitié** est atteignable depuis la position rangée.

Un état est codé par un nombre en base 6 : le chiffre `i` est la pièce de la case `i` (0 = trou),
les cases étant numérotées
```
0 1 2
3 4 5
```

## À prouver
1. `moitie` : exactement 360 configurations sont atteignables.
2. `loyd` : la position rangée avec les pièces 1 et 2 échangées ne l'est pas.""",
"""def chiffre (e i : Nat) : Nat := e / 6 ^ i % 6

def echanger (e i j : Nat) : Nat :=
  e - chiffre e i * 6 ^ i - chiffre e j * 6 ^ j + chiffre e j * 6 ^ i + chiffre e i * 6 ^ j

def voisinsCase : Nat → List Nat
  | 0 => [1, 3] | 1 => [0, 2, 4] | 2 => [1, 5] | 3 => [0, 4] | 4 => [1, 3, 5] | 5 => [2, 4]
  | _ => []

def trou (e : Nat) : Nat := ((List.range 6).find? (chiffre e · == 0)).getD 0

def coups (e : Nat) : List Nat := (voisinsCase (trou e)).map (echanger e (trou e))

/-- Parcours en largeur : `vus` = déjà atteints, `front` = atteints à la dernière étape. -/
def explorer : Nat → List Nat → List Nat → List Nat
  | 0, vus, _ => vus
  | f + 1, vus, front =>
    let nouveaux := ((front.flatMap coups).eraseDups).filter (fun e => !vus.contains e)
    if nouveaux.isEmpty then vus else explorer f (vus ++ nouveaux) nouveaux

/-- `1 2 3 / 4 5 _` -/
def range : Nat := 1 + 2 * 6 + 3 * 6 ^ 2 + 4 * 6 ^ 3 + 5 * 6 ^ 4

/-- `2 1 3 / 4 5 _` -/
def loydPos : Nat := 2 + 1 * 6 + 3 * 6 ^ 2 + 4 * 6 ^ 3 + 5 * 6 ^ 4

theorem moitie : (explorer 30 [range] [range]).length = 360 := by -- @exo
  decide +kernel

theorem loyd : (explorer 30 [range] [range]).contains loydPos = false := by -- @exo
  decide +kernel""",
["Ce sont des explorations exhaustives : `decide +kernel`.", "Pour comprendre l'invariant : chaque coup échange le trou avec une pièce ; la parité de la permutation change à chaque coup, et la parité de la position du trou aussi."], NE, requiert="Enigmes.Missionnaires",
ressources=["[Taquin (Wikipédia)](https://fr.wikipedia.org/wiki/Taquin)"])

exo("Enigmes", "DameTigre", "La dame ou le tigre ?", 1, [LB],
"""Raymond Smullyan, *La dame ou le tigre ?* (1982) : un prisonnier doit choisir entre deux portes.
Derrière chacune se trouve une dame (qu'il épousera) ou un tigre (qui le mangera). Des pancartes
l'aident… ou le trompent. `true` = dame, `false` = tigre.

**Épreuve 1.** Porte 1 : « Dans cette pièce il y a une dame, et dans l'autre un tigre. »
Porte 2 : « Une des pièces contient une dame, et une des pièces contient un tigre. »
On sait qu'**une** pancarte dit vrai et l'autre faux.

**Épreuve 2.** Porte 1 : « Au moins une des pièces contient une dame. »
Porte 2 : « Il y a un tigre dans l'autre pièce. » Les deux pancartes disent toutes deux vrai, ou
toutes deux faux.

**Épreuve 3.** Porte 1 : « Il y a un tigre dans cette pièce, ou une dame dans l'autre. »
Porte 2 : « Il y a une dame dans l'autre pièce. » Toutes deux vraies ou toutes deux fausses.

## À prouver
Pour chaque épreuve, la seule possibilité.""",
"""theorem epreuve1 (d1 d2 : Bool)
    (h : (d1 && !d2) != ((d1 || d2) && (!d1 || !d2))) : d1 = false ∧ d2 = true := by -- @exo
  revert h
  revert d1 d2
  decide

theorem epreuve2 (d1 d2 : Bool) (h : (d1 || d2) = !d1) : d1 = false ∧ d2 = true := by -- @exo
  revert h
  revert d1 d2
  decide

theorem epreuve3 (d1 d2 : Bool) (h : (!d1 || d2) = d1) : d1 = true ∧ d2 = true := by -- @exo
  revert h
  revert d1 d2
  decide""",
["Il n'y a que 4 cas : `revert h`, `revert d1 d2`, puis `decide` les essaie tous.", "Ou à la main : `cases d1 <;> cases d2 <;> simp_all`."], NE, requiert="Enigmes.Chevaliers",
ressources=["[Raymond Smullyan (Wikipédia)](https://fr.wikipedia.org/wiki/Raymond_Smullyan)"])

exo("Enigmes", "Gardiens", "Les deux gardiens", 1, [LB],
"""Deux portes : l'une mène au trésor, l'autre au précipice. Deux gardiens : l'un dit **toujours**
la vérité, l'autre ment **toujours**, et tu ne sais pas lequel est lequel. Tu as droit à **une**
question à **un** gardien. Laquelle ?

Réponse célèbre : montre une porte et demande « Si je demandais à l'autre gardien si cette porte
mène au trésor, que me répondrait-il ? » … et fais le contraire ! Autre solution : « Si je te
demandais si cette porte mène au trésor, que me répondrais-tu ? » Là, la réponse est la vérité.

`repond h p` : la réponse (oui/non) d'un gardien d'honnêteté `h` à une question dont la vraie
réponse est `p`.

## À prouver
1. `demander_a_l_autre : repond h (repond (!h) t) = !t` (la réponse est toujours fausse)
2. `demander_a_soi : repond h (repond h t) = t` (la réponse est toujours juste)""",
"""def repond (honnete p : Bool) : Bool := if honnete then p else !p

theorem demander_a_l_autre (h t : Bool) : repond h (repond (!h) t) = !t := by -- @exo
  cases h <;> cases t <;> rfl

theorem demander_a_soi (h t : Bool) : repond h (repond h t) = t := by -- @exo
  cases h <;> cases t <;> rfl""",
["Quatre cas : `cases h <;> cases t <;> rfl`."], NE, requiert="Enigmes.Chevaliers")

exo("Enigmes", "Tartes", "Qui a volé les tartes ?", 1, [LB, LP],
"""Au pays d'Alice, les tartes de la Reine ont disparu. Trois suspects : le Lièvre de Mars (0), le
Chapelier (1) et le Loir (2). Un seul est coupable. Le coupable ment, les innocents disent la
vérité.
- Le Lièvre : « Le Loir est innocent. »
- Le Chapelier : « C'est le Lièvre qui a volé les tartes. »
- Le Loir : « Le Chapelier ment. »

Qui est le voleur ?

## À prouver
`voleur` : seul le Chapelier est compatible avec les déclarations.""",
"""/-- Les déclarations sont-elles cohérentes si le voleur est `x` ? -/
def coherent (x : Nat) : Bool :=
  let lievre := x != 2
  let chapelier := x == 0
  let loir := !chapelier
  (lievre == (x != 0)) && (chapelier == (x != 1)) && (loir == (x != 2))

theorem voleur : ∀ x, x < 3 → (coherent x = true ↔ x = 1) := by -- @exo
  decide""",
["`decide` essaie les trois suspects."], NE, requiert="Enigmes.Chevaliers")

exo("Enigmes", "Etiquettes", "Les trois boîtes mal étiquetées", 2, [LB, LP],
"""Trois boîtes sont étiquetées « Pommes », « Oranges » et « Mélange ». Toutes les étiquettes sont
**fausses**. Tu peux tirer **un seul** fruit d'**une seule** boîte, sans regarder dedans. Comment
retrouver le contenu des trois boîtes ?

Réponse : tire un fruit dans la boîte « Mélange » ! Elle ne contient pas le mélange, donc le fruit
tiré dit tout. Par exemple, si c'est une orange…

Codage : 0 = pommes, 1 = oranges, 2 = mélange. `c` donne le contenu de chaque boîte, indexée par
son étiquette.

## À prouver
`orange` : si on tire une orange de la boîte « Mélange », la seule possibilité est : la boîte
« Pommes » contient le mélange, la boîte « Oranges » les pommes, la boîte « Mélange » les oranges.""",
"""def contenus : List (List Nat) :=
  [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]

def toutesFausses (c : List Nat) : Bool := (List.range 3).all fun i => c.getD i 0 != i

/-- Tirer un fruit de type `f` dans la boîte d'étiquette `b` est possible. -/
def possible (c : List Nat) (b f : Nat) : Bool := c.getD b 0 == f || c.getD b 0 == 2

theorem orange : ∀ c ∈ contenus, toutesFausses c = true → possible c 2 1 = true → c = [2, 0, 1] := by -- @exo
  decide""",
["`decide` essaie les 6 façons de répartir les contenus."], NE, requiert="Enigmes.Tartes")

NL = "Parcours.Logique"
exo("Logique", "Socrate", "Le syllogisme de Socrate", 1, ["ParcoursOutils"],
"""« Tous les hommes sont mortels. Socrate est un homme. Donc Socrate est mortel. » C'est le
**syllogisme** le plus célèbre (Aristote). En Lean, « tous les hommes sont mortels » est une
fonction qui, à tout `x` et toute preuve que `x` est un homme, associe une preuve que `x` est
mortel.

## À prouver
1. `socrate`
2. `contraposee_zeus` : si Zeus n'est pas mortel, Zeus n'est pas un homme.""",
"""theorem socrate {Etre : Type} (Homme Mortel : Etre → Prop) (socrate : Etre)
    (h1 : ∀ x, Homme x → Mortel x) (h2 : Homme socrate) : Mortel socrate := by -- @exo
  exact h1 socrate h2

theorem contraposee_zeus {Etre : Type} (Homme Mortel : Etre → Prop) (zeus : Etre)
    (h1 : ∀ x, Homme x → Mortel x) (h2 : ¬Mortel zeus) : ¬Homme zeus := by -- @exo
  intro h
  exact h2 (h1 zeus h)""",
["`h1 socrate h2` : on applique « pour tout x » à Socrate.", "Pour la contraposée : `intro h`, puis il faut prouver `False`."], NL, requiert="Logique.PourTout")

exo("Logique", "Carroll", "Les sorites de Lewis Carroll", 1, ["ParcoursOutils"],
"""Lewis Carroll (l'auteur d'*Alice au pays des merveilles*) était aussi logicien. Il inventait des
« sorites » : des chaînes de prémisses absurdes dont il fallait tirer la conclusion.

**Les bébés.** (1) Les bébés sont illogiques. (2) Personne n'est méprisé s'il sait dompter un
crocodile. (3) Les gens illogiques sont méprisés. Conclusion : les bébés ne savent pas dompter les
crocodiles.

**Les canards.** (1) Aucun canard ne danse la valse. (2) Aucun officier ne refuse de danser la
valse. (3) Toutes mes volailles sont des canards. Conclusion : mes volailles ne sont pas
officiers.

## À prouver
`bebes` et `canards`.""",
"""theorem bebes {Gens : Type} (Bebe Logique Meprise Dompteur : Gens → Prop)
    (h1 : ∀ x, Bebe x → ¬Logique x) (h2 : ∀ x, Dompteur x → ¬Meprise x)
    (h3 : ∀ x, ¬Logique x → Meprise x) : ∀ x, Bebe x → ¬Dompteur x := by -- @exo
  intro x hb hd
  exact h2 x hd (h3 x (h1 x hb))

theorem canards {Etre : Type} (Canard Valse Officier Volaille : Etre → Prop)
    (h1 : ∀ x, Canard x → ¬Valse x) (h2 : ∀ x, Officier x → Valse x)
    (h3 : ∀ x, Volaille x → Canard x) : ∀ x, Volaille x → ¬Officier x := by -- @exo
  intro x hv ho
  exact h1 x (h3 x hv) (h2 x ho)""",
["Commence par `intro x hb hd` : il faut alors prouver `False`.", "Enchaîne les prémisses : un bébé est illogique, donc méprisé ; un dompteur n'est pas méprisé."], NL, requiert="Logique.Socrate",
ressources=["[Lewis Carroll, *Symbolic Logic* (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Symbolic_Logic_(book))"])

NC = "Parcours.Classiques"
def cl(ident, titre, diff, imports, image, enonce, code, indices, requiert, ressources=()):
    texte = "## Se le représenter\n" + image.strip() + "\n\n## À prouver\n" + enonce.strip()
    exo("Classiques", ident, titre, diff, imports, texte, code, indices, NC, requiert=requiert, ressources=ressources)

cl("CubesImpairs", "La somme des cubes impairs", 2, [RD],
"""`1³ = 1`, `1³ + 3³ = 28`, `1³ + 3³ + 5³ = 153`… La formule : `n²(2n² − 1)`. Sans soustraction :
`somme + n² = 2n⁴`.""",
"`cubes_impairs : somme (fun i => (2 * i + 1) ^ 3) n + n ^ 2 = 2 * n ^ 4`",
"""open Parcours.Recurrence

theorem cubes_impairs (n : Nat) : somme (fun i => (2 * i + 1) ^ 3) n + n ^ 2 = 2 * n ^ 4 := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ]
    grind""",
["Récurrence ; `somme_succ`, puis `grind`."], "Classiques.CarresImpairs")

cl("PoidsBinaires", "Une somme pondérée par les puissances de 2", 2, [RD],
"""`0·1 + 1·2 + 2·4 + 3·8 = 34 = 2·16 + 2`. La somme `Σ i·2ⁱ` vaut `(n − 2)·2ⁿ + 2` (c'est le nombre
moyen de comparaisons de certains algorithmes « diviser pour régner »). Sans soustraction :
`somme + 2^(n+1) = n·2ⁿ + 2`.""",
"`poids_binaires : somme (fun i => i * 2 ^ i) n + 2 ^ (n + 1) = n * 2 ^ n + 2`",
"""open Parcours.Recurrence

theorem poids_binaires (n : Nat) : somme (fun i => i * 2 ^ i) n + 2 ^ (n + 1) = n * 2 ^ n + 2 := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ, Nat.pow_succ 2 (n + 1), Nat.pow_succ 2 n]
    rw [Nat.pow_succ] at ih
    grind""",
["Récurrence ; `somme_succ` et `Nat.pow_succ`, puis `grind`."], "Classiques.PuissancesTrois")

exo("Programmes", "Heureux", "Les nombres heureux", 1, ["Solutions.Programmes.Definitions"],
"""Prends un nombre, remplace-le par la somme des carrés de ses chiffres, et recommence :
`7 → 49 → 97 → 130 → 10 → 1`. Si on arrive à 1, le nombre est **heureux**. Sinon, on tombe
toujours dans le même cycle : `4 → 16 → 37 → 58 → 89 → 145 → 42 → 20 → 4`.

## À prouver
1. `sept_heureux : repeter carresChiffres 5 7 = 1`
2. `cycle_malheureux : repeter carresChiffres 8 4 = 4`
3. `dix_neuf` : il y a 19 nombres heureux entre 1 et 99.
4. `toujours` : pour tout `0 < n < 1000`, après 20 étapes on est à 1 ou dans le cycle de 4.""",
"""def carresChiffres (n : Nat) : Nat :=
  (n % 10) ^ 2 + (n / 10 % 10) ^ 2 + (n / 100 % 10) ^ 2 + (n / 1000 % 10) ^ 2

def cycle4 : List Nat := [4, 16, 37, 58, 89, 145, 42, 20]

theorem sept_heureux : repeter carresChiffres 5 7 = 1 := by -- @exo
  decide

theorem cycle_malheureux : repeter carresChiffres 8 4 = 4 := by -- @exo
  decide

theorem dix_neuf : ((List.range 100).filter fun n => 0 < n && repeter carresChiffres 20 n == 1).length = 19 := by -- @exo
  decide +kernel

theorem toujours : ∀ n, n < 1000 → 0 < n → repeter carresChiffres 20 n = 1 ∨ repeter carresChiffres 20 n ∈ cycle4 := by -- @exo
  decide +kernel""",
["Des calculs : `decide` / `decide +kernel`.", "Pour comprendre `toujours` : pour un nombre à 4 chiffres, la somme des carrés des chiffres est au plus `4 × 81 = 324` ; tout finit par descendre sous 1000."], "Parcours.Prog", requiert="Programmes.RegarderDire",
ressources=["[Nombre heureux (Wikipédia)](https://fr.wikipedia.org/wiki/Nombre_heureux)"])

ecrire_tout()
