import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fabrique import exo, ecrire_tout

P = "Solutions.Programmes.Definitions"
RD = "Solutions.Recurrence.Definitions"
LP = "Solutions.Listes.Pont"
AD = "Solutions.Arithmetique.Definitions"

def pr(ident, titre, diff, texte, code, indices, requiert, imports=(P,), ressources=()):
    exo("Programmes", ident, titre, diff, list(imports), texte, code, indices, "Parcours.Prog", requiert=requiert, ressources=ressources)

pr("Lame", "Le pire cas de l'algorithme d'Euclide", 3,
"""Combien d'étapes (divisions) l'algorithme d'Euclide fait-il pour calculer un PGCD ? Gabriel Lamé
(1844) a montré que le pire cas est celui de deux nombres de Fibonacci consécutifs : chaque division
ne fait « reculer » que d'un cran dans la suite. C'est le premier résultat de **complexité
algorithmique** de l'histoire.

## À prouver
1. `fib_pos : 0 < fib (n + 1)` et `fib_lt : fib (n + 2) < fib (n + 3)`
2. `fib_mod : fib (n + 4) % fib (n + 3) = fib (n + 2)`
3. `lame : etapes (fib (n + 3)) (fib (n + 2)) = n + 1`""",
"""open Parcours.Recurrence

def etapes (a b : Nat) : Nat := if h : b = 0 then 0 else 1 + etapes b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (by omega)

theorem fib_pos (n : Nat) : 0 < fib (n + 1) := by -- @exo
  have : ∀ n, 0 < fib (n + 1) ∧ 0 < fib (n + 2) := by
    intro n
    induction n with
    | zero => decide
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [show n + 1 + 2 = n + 3 from rfl, show n + 3 = (n + 1) + 2 from rfl, fib_add_two]
      omega
  exact (this n).1

theorem fib_lt (n : Nat) : fib (n + 2) < fib (n + 3) := by -- @exo
  rw [show n + 3 = (n + 1) + 2 from rfl, fib_add_two]
  show fib (n + 2) < fib (n + 1) + fib (n + 2)
  have := fib_pos n
  omega

theorem fib_mod (n : Nat) : fib (n + 4) % fib (n + 3) = fib (n + 2) := by -- @exo
  rw [show n + 4 = (n + 2) + 2 from rfl, fib_add_two, show n + 2 + 1 = n + 3 from rfl,
    Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (fib_lt n)

theorem lame (n : Nat) : etapes (fib (n + 3)) (fib (n + 2)) = n + 1 := by -- @exo
  induction n with
  | zero =>
    show etapes 2 1 = 1
    rw [etapes]
    simp only [show (1 : Nat) ≠ 0 by decide, ↓reduceDIte]
    rw [show 2 % 1 = 0 from rfl, etapes]
    simp
  | succ n ih =>
    rw [show n + 1 + 3 = n + 4 from rfl, show n + 1 + 2 = n + 3 from rfl, etapes]
    have h : fib (n + 3) ≠ 0 := Nat.ne_of_gt (fib_pos (n + 2))
    simp only [h, ↓reduceDIte]
    rw [fib_mod, ih]
    omega""",
["`fib_pos` : prouve en même temps `0 < fib (n + 1)` et `0 < fib (n + 2)` par récurrence.", "`fib_mod` : `fib (n + 4) = fib (n + 2) + fib (n + 3)`, et `Nat.add_mod_right`, `Nat.mod_eq_of_lt`.", "`lame` : déplie `etapes` avec `rw [etapes]`, puis l'hypothèse de récurrence."], "Programmes.DivisionSoustraction",
ressources=["[Théorème de Lamé (Wikipédia)](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_de_Lam%C3%A9)"])

pr("Regle90", "La règle 90 et le triangle de Sierpiński", 1,
"""Un **automate cellulaire** sur une ligne : chaque case devient vivante si exactement une de ses
deux voisines l'était (OU exclusif). En partant d'une seule case vivante, on voit apparaître le
**triangle de Sierpiński**… qui n'est autre que le triangle de Pascal **modulo 2** !
```
        █
       █ █
      █   █
     █ █ █ █
    █       █
```

## À prouver
`sierpinski` : pour les 16 premières lignes, la règle 90 donne le triangle de Pascal modulo 2
(avec une case vide entre deux coefficients).""",
"""/-- Une génération : la ligne s'allonge d'une case de chaque côté. -/
def regle90 (l : List Bool) : List Bool := List.zipWith (· ^^ ·) (false :: false :: l) (l ++ [false, false])

/-- `[a, b, c]` ↦ `[a, false, b, false, c]` -/
def intercaler : List Bool → List Bool
  | [] => []
  | [a] => [a]
  | a :: r => a :: false :: intercaler r

theorem sierpinski : ∀ n, n < 16 →
    repeter regle90 n [true] = intercaler ((pascal n).map (· % 2 == 1)) := by -- @exo
  decide +kernel""",
["Un calcul : `decide +kernel`.", "Pourquoi ? Dans Pascal, chaque coefficient est la somme de ses deux voisins du dessus ; modulo 2, une somme devient un OU exclusif."], "Programmes.Pascal", imports=(P, "Solutions.Programmes.Pascal"),
ressources=["[Règle 90 (Wikipédia)](https://fr.wikipedia.org/wiki/R%C3%A8gle_90)"])

pr("Voyageur", "Le voyageur de commerce", 2,
"""Un voyageur part de la ville 0, doit visiter les villes 1, 2, 3, 4 et revenir. Quel est le plus
court circuit ? Avec 5 villes, on peut tout essayer (24 ordres) ; avec 30 villes, il y aurait plus
de circuits que d'atomes dans l'univers. Ce problème est **NP-difficile** : on ne connaît aucun
algorithme rapide, et il y a un million de dollars à gagner (problème P = NP) pour qui en trouve un
ou prouve qu'il n'en existe pas.

## À faire
Trouve `meilleurTour` (l'ordre de visite des villes 1 à 4) et prouve `optimal`.""",
"""open Parcours.Combi

def distances : List (List Nat) :=
  [[0, 2, 9, 10, 7], [2, 0, 6, 4, 3], [9, 6, 0, 8, 5], [10, 4, 8, 0, 6], [7, 3, 5, 6, 0]]

def dist (a b : Nat) : Nat := (distances.getD a []).getD b 0

def longueurTour (t : List Nat) : Nat := (((0 :: t).zip (t ++ [0])).map fun p => dist p.1 p.2).sum

def meilleurTour : List Nat := -- @exo
  [1, 3, 2, 4]

theorem optimal : meilleurTour.isPerm [1, 2, 3, 4] = true ∧ longueurTour meilleurTour = 26 ∧
    ∀ t ∈ perms [1, 2, 3, 4], 26 ≤ longueurTour t := by -- @exo
  decide""",
["Commence par les petites distances : 0 → 1 coûte 2, 1 → 3 coûte 4…", "`perms` vient de l'exercice « Les anagrammes »."], "Combinatoire.Anagrammes", imports=(P, "Solutions.Combinatoire.Anagrammes"),
ressources=["[Problème du voyageur de commerce (Wikipédia)](https://fr.wikipedia.org/wiki/Probl%C3%A8me_du_voyageur_de_commerce)"])

pr("Labyrinthe", "Sortir du labyrinthe", 2,
"""Le parcours **en largeur** trouve le plus court chemin dans un labyrinthe : on explore d'abord
toutes les cases à distance 1, puis 2, etc. (comme une tache d'encre qui s'étale).
```
S . # . .
. # # . #
. . . # .
# . # . .
. . . . E
```
Les cases sont numérotées `5 × ligne + colonne` ; `S` = 0, `E` = 24.

## À faire
1. Écris `cheminSortie` (la suite des cases, de 0 à 24) et prouve `chemin_ok`.
2. `plus_court` : le parcours en largeur trouve 8, donc ton chemin (8 pas) est optimal.""",
"""def murs : List Bool :=
  [false, false, true, false, false,
   false, true, true, false, true,
   false, false, false, true, false,
   true, false, true, false, false,
   false, false, false, false, false]

def libre (p : Nat) : Bool := p < 25 && !murs.getD p true

def voisinsL (p : Nat) : List Nat :=
  ((if p % 5 = 0 then [] else [p - 1]) ++ (if p % 5 = 4 then [] else [p + 1]) ++
    (if p < 5 then [] else [p - 5]) ++ [p + 5]).filter libre

def cheminOk : List Nat → Bool
  | a :: b :: r => (voisinsL a).contains b && cheminOk (b :: r)
  | _ => true

/-- Parcours en largeur : distance de la sortie (`f` : réserve). -/
def distance : Nat → List Nat → List Nat → Nat → Option Nat
  | 0, _, _, _ => none
  | f + 1, vus, front, d =>
    if front.contains 24 then some d
    else
      let nouveaux := ((front.flatMap voisinsL).eraseDups).filter (fun p => !vus.contains p)
      if nouveaux.isEmpty then none else distance f (vus ++ nouveaux) nouveaux (d + 1)

def cheminSortie : List Nat := -- @exo
  [0, 5, 10, 11, 16, 21, 22, 23, 24]

theorem chemin_ok : cheminSortie.head? = some 0 ∧ cheminSortie.getLast? = some 24 ∧
    cheminOk cheminSortie = true ∧ cheminSortie.length = 9 := by -- @exo
  decide

theorem plus_court : distance 30 [0] [0] 0 = some 8 := by -- @exo
  decide""",
["Descends d'abord le long du bord gauche.", "`plus_court` est un calcul : `decide`."], "Programmes.Reines",
ressources=["[Algorithme de parcours en largeur (Wikipédia)](https://fr.wikipedia.org/wiki/Algorithme_de_parcours_en_largeur)"])

pr("SacADos", "Le sac à dos", 3,
"""Un cambrioleur a un sac qui supporte 10 kg. Quels objets emporter pour maximiser la valeur ?
La **programmation dynamique** (Bellman, années 1950) répond avec une équation : pour le premier
objet, soit on le laisse, soit on le prend (s'il rentre), et on garde le meilleur des deux.

On prouve que cette équation donne vraiment l'optimum : elle majore la valeur de **tout** choix
d'objets possible, et elle est atteinte.

## À prouver
1. `sac_majore` : aucun choix qui rentre dans le sac ne vaut plus que `sac l c`.
2. `sac_atteint` : il existe un choix qui atteint `sac l c`.
3. `cambriolage : sac objets 10 = 113`""",
"""/-- Les objets sont des couples (poids, valeur). -/
def sac : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | (w, v) :: r, c => if w ≤ c then max (sac r c) (v + sac r (c - w)) else sac r c

def parties {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: l => parties l ++ (parties l).map (x :: ·)

def poidsSac (s : List (Nat × Nat)) : Nat := (s.map Prod.fst).sum
def valeurSac (s : List (Nat × Nat)) : Nat := (s.map Prod.snd).sum

theorem sac_majore (l : List (Nat × Nat)) (c : Nat) :
    ∀ s ∈ parties l, poidsSac s ≤ c → valeurSac s ≤ sac l c := by -- @exo
  induction l generalizing c with
  | nil =>
    intro s hs _
    simp [parties] at hs
    subst hs
    simp [valeurSac]
  | cons x l ih =>
    intro s hs hp
    obtain ⟨w, v⟩ := x
    simp only [parties, List.mem_append, List.mem_map] at hs
    simp only [sac]
    rcases hs with hs | ⟨s', hs', rfl⟩
    · have := ih c s hs hp
      split <;> omega
    · simp only [poidsSac, valeurSac, List.map_cons, List.sum_cons] at hp ⊢
      have := ih (c - w) s' hs' (by unfold poidsSac; omega)
      unfold valeurSac at this
      split <;> omega

theorem sac_atteint (l : List (Nat × Nat)) (c : Nat) :
    ∃ s ∈ parties l, poidsSac s ≤ c ∧ valeurSac s = sac l c := by -- @exo
  induction l generalizing c with
  | nil => exact ⟨[], by simp [parties], by simp [poidsSac], by simp [valeurSac, sac]⟩
  | cons x l ih =>
    obtain ⟨w, v⟩ := x
    obtain ⟨s1, h1, p1, v1⟩ := ih c
    simp only [sac]
    split
    · rename_i hw
      obtain ⟨s2, h2, p2, v2⟩ := ih (c - w)
      by_cases hm : sac l c ≤ v + sac l (c - w)
      · refine ⟨(w, v) :: s2, ?_, ?_, ?_⟩
        · simp only [parties, List.mem_append, List.mem_map]
          exact Or.inr ⟨s2, h2, rfl⟩
        · simp only [poidsSac, List.map_cons, List.sum_cons] at p2 ⊢
          omega
        · simp only [valeurSac, List.map_cons, List.sum_cons] at v2 ⊢
          omega
      · refine ⟨s1, ?_, p1, ?_⟩
        · simp only [parties, List.mem_append]
          exact Or.inl h1
        · omega
    · refine ⟨s1, ?_, p1, v1⟩
      simp only [parties, List.mem_append]
      exact Or.inl h1

def objets : List (Nat × Nat) := [(5, 10), (4, 40), (6, 30), (3, 50), (2, 15), (1, 8)]

theorem cambriolage : sac objets 10 = 113 := by -- @exo
  decide""",
["Les deux théorèmes : récurrence sur la liste d'objets, en généralisant la capacité `c`.", "Un choix de `parties (x :: l)` est soit un choix de `parties l`, soit `x :: s'` ; dans le second cas, `s'` rentre dans un sac de capacité `c − w`.", "`omega` sait raisonner avec `max`."], "Programmes.Monnaie",
ressources=["[Problème du sac à dos (Wikipédia)](https://fr.wikipedia.org/wiki/Probl%C3%A8me_du_sac_%C3%A0_dos)"])

exo("Enigmes", "SudokuUnique", "Un sudoku à solution unique", 2, ["Solutions.Enigmes.Sudoku"],
"""Un bon sudoku n'a qu'**une** solution. Celui-ci n'a que 4 indices, et pourtant sa solution est
unique ! On le prouve avec un **solveur** par retour sur trace : on remplit la première case vide
avec chaque valeur compatible, et on continue récursivement.
```
. . | . 4
3 . | . .
----+----
2 . | . .
. . | . 1
```

## À prouver
`unique_solution : resoudre 16 grilleDure = [ … la solution … ]`""",
"""def compatibleS (g : List Nat) (i v : Nat) : Bool :=
  groupesSudoku.all fun gr => !(gr.contains i) || gr.all fun j => g.getD j 0 != v

def resoudre : Nat → List Nat → List (List Nat)
  | 0, g => if g.contains 0 then [] else [g]
  | f + 1, g =>
    match g.findIdx? (· == 0) with
    | none => [g]
    | some i => ([1, 2, 3, 4].filter (compatibleS g i)).flatMap fun v => resoudre f (g.set i v)

def grilleDure : List Nat := [0, 0, 0, 4, 3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1]

theorem unique_solution :
    resoudre 16 grilleDure = [[1, 2, 3, 4, 3, 4, 1, 2, 2, 1, 4, 3, 4, 3, 2, 1]] := by -- @exo
  decide +kernel""",
["Un calcul : `decide +kernel` fait tourner le solveur.", "Essaie `#eval resoudre 16 [0, 2, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 2, 0]` : la grille de l'exercice « Un petit sudoku » a 4 solutions !"], "Parcours.Enigmes", requiert="Enigmes.Sudoku")

NC = "Parcours.Classiques"
exo("Classiques", "Boulets", "La pile de boulets de canon", 2, ["Solutions.Classiques.Triangulaires", "Solutions.Classiques.CarresGrille"],
"""## Se le représenter
Une pile de boulets de canon à base **triangulaire** : chaque étage est un nombre triangulaire
(1, 3, 6, 10…). Le nombre total de boulets est un **nombre tétraédrique** : `1, 4, 10, 20, 35…`,
égal à `n(n+1)(n+2)/6`.

Pour une pile à base **carrée**, on additionne des carrés. Édouard Lucas (1875) a demandé : quand
une pile carrée contient-elle un nombre **carré** de boulets ? Seulement pour 1 étage… et pour
24 étages : `1² + 2² + ⋯ + 24² = 4900 = 70²` !

## À prouver
1. `tetraedrique : 6 * somme tri (n + 1) = n * (n + 1) * (n + 2)`
2. `lucas : carres 24 = 70 ^ 2`""",
"""open Parcours.Recurrence

theorem tetraedrique (n : Nat) : 6 * somme tri (n + 1) = n * (n + 1) * (n + 2) := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ, Nat.mul_add, ih]
    have g := gauss (n + 1)
    unfold tri
    grind

theorem lucas : carres 24 = 70 ^ 2 := by -- @exo
  decide""",
["Récurrence ; `somme_succ`, et la formule de Gauss pour `tri (n + 1)`.", "`lucas` : `decide`."], NC, requiert="Classiques.CarresGrille",
ressources=["[Problème des boulets de canon (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Cannonball_problem)"])

exo("Classiques", "ZerosFactorielle", "Les zéros de 100!", 1, [RD],
"""## Se le représenter
Par combien de zéros se termine `100! = 1 × 2 × ⋯ × 100` (un nombre de 158 chiffres) ? Chaque zéro
vient d'un facteur `10 = 2 × 5`, et il y a bien plus de 2 que de 5. On compte donc les 5 : les
multiples de 5 en apportent un (20 nombres), les multiples de 25 un second (4 nombres) : **24**
zéros (formule de Legendre).

## À prouver
1. `legendre : 100 / 5 + 100 / 25 = 24`
2. `vingt_quatre` : `100!` est divisible par `10²⁴` mais pas par `10²⁵`.""",
"""open Parcours.Recurrence

theorem legendre : 100 / 5 + 100 / 25 = 24 := by -- @exo
  decide

theorem vingt_quatre : fact 100 % 10 ^ 24 = 0 ∧ fact 100 % 10 ^ 25 ≠ 0 := by -- @exo
  decide""",
["`decide` calcule même `100!`."], NC, requiert="Recurrence.SommeFactorielles")

NA = "Parcours.Arith"
exo("Arithmetique", "WilsonPetits", "Le théorème de Wilson, vérifié", 1, [AD],
"""Le théorème de Wilson (1770) : `p` est premier si et seulement si `(p − 1)! + 1` est divisible par
`p`. C'est un test de primalité parfait… mais inutilisable en pratique (calculer `(p − 1)!` est
bien trop long). Vérifions-le pour les petits nombres.

## À prouver
`wilson_petits : ∀ p < 40, 2 ≤ p → ((fact (p - 1) + 1) % p = 0 ↔ estPremierB p = true)`""",
"""open Parcours.Recurrence

def estPremierB (p : Nat) : Bool := 2 ≤ p && (List.range p).all fun d => d < 2 || p % d != 0

theorem wilson_petits : ∀ p, p < 40 → 2 ≤ p → ((fact (p - 1) + 1) % p = 0 ↔ estPremierB p = true) := by -- @exo
  decide +kernel""",
["Un calcul : `decide +kernel`."], NA, requiert="Arithmetique.TestPrimalite",
ressources=["[Théorème de Wilson (Wikipédia)](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_de_Wilson)"])

exo("Arithmetique", "Carmichael", "Le menteur 561", 2, ["Solutions.Informatique.RSA"],
"""Le petit théorème de Fermat dit : si `p` est premier, alors `aᵖ⁻¹ ≡ 1 (mod p)` pour tout `a` non
multiple de `p`. La réciproque est **fausse** ! `561 = 3 × 11 × 17` n'est pas premier, mais
`a⁵⁶⁰ ≡ 1 (mod 561)` pour **tous** les `a` premiers avec 561. C'est le plus petit **nombre de
Carmichael** (1910). Les tests de primalité modernes (Miller-Rabin) doivent déjouer ces menteurs.

## À prouver
1. `compose : 561 = 3 * 11 * 17`
2. `menteur` : pour tout `a < 561` premier avec 561, `a⁵⁶⁰ mod 561 = 1`.""",
"""open Parcours.Info

theorem compose : 561 = 3 * 11 * 17 := by -- @exo
  decide

theorem menteur : ∀ a, a < 561 → a % 3 ≠ 0 → a % 11 ≠ 0 → a % 17 ≠ 0 →
    puissMod 20 a 560 561 = 1 := by -- @exo
  decide +kernel""",
["Un calcul : `decide +kernel` (avec l'exponentiation rapide de « RSA en miniature »).", "Pourquoi ? 560 est multiple de `2`, `10` et `16`, c'est-à-dire de `3 − 1`, `11 − 1` et `17 − 1` (critère de Korselt)."], NA, requiert="Informatique.RSA",
ressources=["[Nombre de Carmichael (Wikipédia)](https://fr.wikipedia.org/wiki/Nombre_de_Carmichael)"])

ecrire_tout()
