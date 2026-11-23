import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fabrique import exo, ecrire_tout

RD = "Solutions.Recurrence.Definitions"
LP = "Solutions.Listes.Pont"
C = "Solutions.Circuits.Definitions"
NCI = "Parcours.Circuits"

exo("Circuits", "Nand", "La porte NAND est universelle", 1, [C],
"""Une seule porte logique suffit pour fabriquer **tous** les circuits : la porte NAND
(« non-et » : `nand a b = !(a && b)`). Les puces électroniques sont d'ailleurs construites
presque uniquement avec des NAND (ou des NOR).

## À prouver
Que les circuits construits avec des NAND calculent bien NON, ET, OU et OU exclusif.""",
"""def nand (a b : Bool) : Bool := !(a && b)

def non (a : Bool) : Bool := nand a a
def et (a b : Bool) : Bool := nand (nand a b) (nand a b)
def ou (a b : Bool) : Bool := nand (nand a a) (nand b b)
def ouex (a b : Bool) : Bool := nand (nand a (nand a b)) (nand b (nand a b))

theorem non_ok (a : Bool) : non a = !a := by -- @exo
  cases a <;> rfl

theorem et_ok (a b : Bool) : et a b = (a && b) := by -- @exo
  cases a <;> cases b <;> rfl

theorem ou_ok (a b : Bool) : ou a b = (a || b) := by -- @exo
  cases a <;> cases b <;> rfl

theorem ouex_ok (a b : Bool) : ouex a b = xor a b := by -- @exo
  cases a <;> cases b <;> rfl""",
["Tous les cas : `cases a <;> cases b <;> rfl` (ou `decide` après `revert a b`)."], NCI, requiert="Circuits.Additionneurs",
ressources=["[Fonction NON-ET (Wikipédia)](https://fr.wikipedia.org/wiki/Fonction_NON-ET)"])

exo("Circuits", "Soustracteur", "Le soustracteur complet", 1, [C],
"""Pour soustraire en binaire, on procède comme à l'école, avec une **retenue** (un « emprunt ») :
`a − b − emprunt`. Le résultat est un bit de différence et un nouvel emprunt.

## À prouver
`soustracteur_ok : a + 2 × emprunt_sortant = b + emprunt_entrant + différence` (en valeurs
`0`/`1`).""",
"""def difference (a b e : Bool) : Bool := xor (xor a b) e
def emprunt (a b e : Bool) : Bool := (!a && b) || (!(xor a b) && e)

theorem soustracteur_ok (a b e : Bool) :
    a.toNat + 2 * (emprunt a b e).toNat = b.toNat + e.toNat + (difference a b e).toNat := by -- @exo
  cases a <;> cases b <;> cases e <;> rfl""",
["Huit cas : `cases a <;> cases b <;> cases e <;> rfl`."], NCI, requiert="Circuits.Nand")

exo("Circuits", "Multiplexeur", "Le multiplexeur", 1, [C],
"""Un **multiplexeur** est un aiguillage : un bit de sélection `s` choisit laquelle des deux entrées
passe à la sortie. Avec deux bits de sélection et trois multiplexeurs, on choisit parmi 4 entrées :
c'est ainsi qu'un processeur lit une case de mémoire à partir de son adresse.

## À prouver
1. `mux_ok : mux s a b = if s then b else a`
2. `mux4_ok` : le multiplexeur à 4 entrées choisit l'entrée numéro `2 s₁ + s₀`.""",
"""def mux (s a b : Bool) : Bool := (!s && a) || (s && b)

def mux4 (s1 s0 a b c d : Bool) : Bool := mux s1 (mux s0 a b) (mux s0 c d)

theorem mux_ok (s a b : Bool) : mux s a b = if s then b else a := by -- @exo
  cases s <;> cases a <;> cases b <;> rfl

theorem mux4_ok (s1 s0 a b c d : Bool) :
    mux4 s1 s0 a b c d = [a, b, c, d].getD (2 * s1.toNat + s0.toNat) false := by -- @exo
  cases s1 <;> cases s0 <;> simp [mux4, mux_ok]""",
["`mux_ok` : tous les cas.", "`mux4_ok` : quatre cas pour la sélection, puis `simp [mux4, mux_ok]`."], NCI, requiert="Circuits.Nand")

exo("Logique", "Quantificateurs", "« Tout le monde aime quelqu'un »", 2, ["ParcoursOutils"],
"""« Il existe quelqu'un que tout le monde aime » entraîne « tout le monde aime quelqu'un ». Mais
la réciproque est **fausse** : chacun peut aimer une personne différente ! L'ordre des
quantificateurs `∀` et `∃` compte.

## À prouver
1. `inversion : (∃ y, ∀ x, R x y) → ∀ x, ∃ y, R x y`
2. `pas_reciproque` : avec `R x y := (x = y)` sur `Bool`, chacun « s'aime lui-même » mais personne
   n'est aimé de tous.""",
"""theorem inversion {α : Type} (R : α → α → Prop) (h : ∃ y, ∀ x, R x y) : ∀ x, ∃ y, R x y := by -- @exo
  intro x
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy x⟩

theorem pas_reciproque : (∀ x : Bool, ∃ y : Bool, x = y) ∧ ¬ ∃ y : Bool, ∀ x : Bool, x = y := by -- @exo
  refine ⟨fun x => ⟨x, rfl⟩, ?_⟩
  intro ⟨y, hy⟩
  have h1 := hy true
  have h2 := hy false
  rw [← h1] at h2
  exact Bool.noConfusion h2""",
["`inversion` : `obtain ⟨y, hy⟩ := h`, puis `y` convient pour tout `x`.", "`pas_reciproque` : si `y` était égal à tout le monde, il serait égal à `true` et à `false`."], "Parcours.Logique", requiert="Logique.Carroll")

exo("Probabilites", "Sicherman", "Les dés de Sicherman", 1, ["Solutions.Probabilites.Definitions"],
"""Deux dés bizarres : l'un porte `1, 2, 2, 3, 3, 4`, l'autre `1, 3, 4, 5, 6, 8`. Surprise : la
somme de ces deux dés a **exactement** la même loi que la somme de deux dés ordinaires ! (George
Sicherman, 1978 ; c'est la seule autre paire possible avec des faces positives.)

## À prouver
`sicherman` : pour chaque total de 2 à 12, il y a autant de façons de l'obtenir.""",
"""def deS1 : List Nat := [1, 2, 2, 3, 3, 4]
def deS2 : List Nat := [1, 3, 4, 5, 6, 8]

def sommes (x y : List Nat) : List Nat := x.flatMap fun a => y.map fun b => a + b

theorem sicherman : ∀ s, s < 13 → (sommes deS1 deS2).count s = (sommes de de).count s := by -- @exo
  decide""",
["Un calcul : `decide`."], "Parcours.Proba", requiert="Probabilites.Des",
ressources=["[Dés de Sicherman (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Sicherman_dice)"])

exo("Graphes", "Petersen", "Le graphe de Petersen", 2, ["Solutions.Graphes.Definitions"],
"""Le graphe de Petersen (1898) est le contre-exemple préféré des théoriciens des graphes : 10
sommets, 15 arêtes, chaque sommet a 3 voisins, il n'a ni triangle ni carré… Un pentagone extérieur
(0–4), une étoile intérieure (5–9), et des rayons.

## À prouver
1. `quinze_aretes`, `trois_voisins`
2. `sans_triangle` : aucun triangle.
3. `trois_couleurs` : on peut le colorier avec 3 couleurs, mais `pas_deux` : pas avec 2 (il contient
   un cycle de longueur 5).""",
"""def petersen : Graphe :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5),
   (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)]

def adjacents (g : Graphe) (u v : Nat) : Bool := g.contains (u, v) || g.contains (v, u)

theorem quinze_aretes : petersen.length = 15 := by -- @exo
  decide

theorem trois_voisins : (List.range 10).all (fun v => degre petersen v == 3) = true := by -- @exo
  decide

theorem sans_triangle : ∀ a, a < 10 → ∀ b, b < 10 → ∀ c, c < 10 →
    !(adjacents petersen a b && adjacents petersen b c && adjacents petersen a c) = true := by -- @exo
  decide +kernel

def couleurs3 : List Nat := [0, 1, 0, 1, 2, 1, 2, 2, 0, 0]

theorem trois_couleurs : petersen.all (fun e => couleurs3.getD e.1 0 != couleurs3.getD e.2 0) = true := by -- @exo
  decide

def colorations2 : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (colorations2 n).flatMap fun c => [false :: c, true :: c]

theorem pas_deux : ∀ c ∈ colorations2 10, petersen.any (fun e => c.getD e.1 false == c.getD e.2 false) = true := by -- @exo
  decide +kernel""",
["Tout se vérifie par le calcul : `decide` / `decide +kernel`.", "Pour `pas_deux` : il y a `2¹⁰ = 1024` façons de colorier avec 2 couleurs ; dans chacune, une arête a ses deux bouts de la même couleur."], "Parcours.Graphes", requiert="Graphes.Coloriage",
ressources=["[Graphe de Petersen (Wikipédia)](https://fr.wikipedia.org/wiki/Graphe_de_Petersen)"])

exo("Matrices", "Rotation", "Le quart de tour", 1, ["Solutions.Matrices.Definitions"],
"""La matrice `R = ((0, −1), (1, 0))` fait tourner le plan d'un quart de tour. Quatre quarts de tour
font un tour complet : `R⁴ = I`. Et `R² = −I` : un demi-tour change chaque vecteur en son opposé,
comme `i² = −1` pour les nombres complexes !

Une matrice **nilpotente** : `N = ((0, 1), (0, 0))` n'est pas nulle, mais `N² = 0`.

## À prouver
`demi_tour`, `tour_complet`, `nilpotente`, `det_rotation`.""",
"""open M2

def R : M2 := ⟨0, -1, 1, 0⟩
def N : M2 := ⟨0, 1, 0, 0⟩

theorem demi_tour : R * R = ⟨-1, 0, 0, -1⟩ := by -- @exo
  decide

theorem tour_complet : puiss R 4 = id2 := by -- @exo
  decide

theorem nilpotente : N ≠ ⟨0, 0, 0, 0⟩ ∧ N * N = ⟨0, 0, 0, 0⟩ := by -- @exo
  decide

theorem det_rotation : det R = 1 := by -- @exo
  decide""",
["Des calculs sur des matrices concrètes : `decide`."], "Parcours.Matrices", requiert="Matrices.Associativite")

ecrire_tout()
