import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fabrique import exo, ecrire_tout

RD = "Solutions.Recurrence.Definitions"
LP = "Solutions.Listes.Pont"
AD = "Solutions.Arithmetique.Definitions"
CD = "Solutions.Combinatoire.Definitions"
NC = "Parcours.Classiques"
NA = "Parcours.Arith"

exo("Classiques", "FibPair", "Un Fibonacci sur trois est pair", 2, [RD],
"""## Se le représenter
`0, 1, 1, 2, 3, 5, 8, 13, 21, 34…` : pair, impair, impair, pair, impair, impair… Le motif se
répète car impair + impair = pair, impair + pair = impair, pair + impair = impair.

## À prouver
1. `motif : fib (3k) % 2 = 0 ∧ fib (3k + 1) % 2 = 1 ∧ fib (3k + 2) % 2 = 1`
2. `fib_pair : fib n % 2 = 0 ↔ n % 3 = 0`""",
"""open Parcours.Recurrence

theorem motif (k : Nat) : fib (3 * k) % 2 = 0 ∧ fib (3 * k + 1) % 2 = 1 ∧ fib (3 * k + 2) % 2 = 1 := by -- @exo
  induction k with
  | zero => decide
  | succ k ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have e0 : fib (3 * (k + 1)) = fib (3 * k + 1) + fib (3 * k + 2) := by
      rw [show 3 * (k + 1) = (3 * k + 1) + 2 by omega, fib_add_two]
    have e1 : fib (3 * (k + 1) + 1) = fib (3 * k + 2) + fib (3 * (k + 1)) := by
      rw [show 3 * (k + 1) + 1 = (3 * k + 2) + 2 by omega, fib_add_two]
      rfl
    have e2 : fib (3 * (k + 1) + 2) = fib (3 * (k + 1)) + fib (3 * (k + 1) + 1) := fib_add_two _
    omega

theorem fib_pair (n : Nat) : fib n % 2 = 0 ↔ n % 3 = 0 := by -- @exo
  obtain ⟨h0, h1, h2⟩ := motif (n / 3)
  have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases this with h | h | h
  · rw [show n = 3 * (n / 3) by omega]
    omega
  · rw [show n = 3 * (n / 3) + 1 by omega]
    omega
  · rw [show n = 3 * (n / 3) + 2 by omega]
    omega""",
["`motif` : récurrence sur `k`, avec `fib_add_two` pour écrire les trois termes suivants.", "`fib_pair` : écris `n = 3q`, `3q + 1` ou `3q + 2`."], NC, requiert="Classiques.FibSomme")

exo("Classiques", "TroisCentSoixante", "Pourquoi 360 degrés ?", 1, [LP, RD],
"""## Se le représenter
Les Babyloniens ont choisi de diviser le cercle en 360 degrés. Une bonne raison : 360 a énormément
de diviseurs (24 : on peut partager un tour en 2, 3, 4, 5, 6, 8, 9, 10, 12… parts égales), plus
que tout nombre plus petit. C'est un nombre « hautement composé ».

## À prouver
1. `diviseurs_360 : nbDiviseurs 360 = 24`
2. `record : ∀ n < 360, nbDiviseurs n < 24`""",
"""def nbDiviseurs (n : Nat) : Nat := ((List.range (n + 1)).filter fun d => 0 < d && n % d == 0).length

theorem diviseurs_360 : nbDiviseurs 360 = 24 := by -- @exo
  decide

theorem record : ∀ n, n < 360 → nbDiviseurs n < 24 := by -- @exo
  decide +kernel""",
["Des calculs : `decide` / `decide +kernel`."], NC, requiert="Classiques.Criteres",
ressources=["[Nombre hautement composé (Wikipédia)](https://fr.wikipedia.org/wiki/Nombre_hautement_compos%C3%A9)"])

exo("Arithmetique", "Goldbach100", "Goldbach, vérifié", 1, [AD, LP],
"""La conjecture de Goldbach (1742) : tout nombre pair supérieur à 2 est la somme de deux nombres
premiers (`4 = 2 + 2`, `28 = 5 + 23`…). Elle est vérifiée par ordinateur jusqu'à `4 × 10¹⁸`, mais
**personne** ne sait la prouver (voir la branche Problèmes ouverts). Vérifions-la jusqu'à 200, et
regardons les nombres premiers jumeaux.

## À prouver
1. `goldbach_200` : tout pair de 4 à 200 est somme de deux premiers.
2. `jumeaux_100` : les couples de premiers jumeaux `(p, p + 2)` sous 100.""",
"""def premierB (p : Nat) : Bool := 2 ≤ p && (List.range p).all fun d => d < 2 || p % d != 0

def decomposable (n : Nat) : Bool := (List.range n).any fun p => premierB p && premierB (n - p)

theorem goldbach_200 : ∀ k, k < 99 → decomposable (2 * k + 4) = true := by -- @exo
  decide +kernel

theorem jumeaux_100 : ((List.range 100).filter fun p => premierB p && premierB (p + 2)) =
    [3, 5, 11, 17, 29, 41, 59, 71] := by -- @exo
  decide +kernel""",
["Des calculs : `decide +kernel`."], NA, requiert="Arithmetique.TestPrimalite",
ressources=["[Conjecture de Goldbach (Wikipédia)](https://fr.wikipedia.org/wiki/Conjecture_de_Goldbach)"])

exo("Arithmetique", "Bertrand", "Le postulat de Bertrand, vérifié", 1, ["Solutions.Arithmetique.Goldbach100"],
"""Joseph Bertrand a conjecturé en 1845 qu'entre `n` et `2n` (strictement, pour `n ≥ 2`), il y a toujours un nombre premier.
Tchebychev l'a prouvé en 1852 ; on dit encore « postulat ». La preuve de Paul Erdős (1932, à
19 ans !) est un bijou… mais longue. Vérifions-le pour les petits `n`.

## À prouver
`bertrand_petits : ∀ n, 2 ≤ n → n < 60 → ∃ p, p < 2 * n ∧ n < p ∧ premierB p`""",
"""theorem bertrand_petits : ∀ n, n < 60 → 2 ≤ n → ∃ p, p < 2 * n ∧ n < p ∧ premierB p = true := by -- @exo
  decide +kernel""",
["Un calcul : `decide +kernel` cherche le premier pour chaque `n`."], NA, requiert="Arithmetique.Goldbach100",
ressources=["[Postulat de Bertrand (Wikipédia)](https://fr.wikipedia.org/wiki/Postulat_de_Bertrand)"])

exo("Combinatoire", "UnEuro", "Combien de façons de payer 1 € ?", 2, [CD],
"""Avec des pièces de 1, 2, 5, 10, 20 et 50 centimes, combien de façons de faire exactement 1 € ?
Il y en a **4562** ! On compte avec une récurrence : les façons de payer `n` avec les pièces
`p :: ps` sont celles qui n'utilisent pas `p`, plus celles qui en utilisent au moins une.

## À prouver
1. `facons_un_euro : facons 100 [1, 2, 5, 10, 20, 50] = 4562`
2. `pieces_1_2 : facons n [1, 2] = n / 2 + 1` (avec des 1 et des 2, on choisit juste le nombre de 2)""",
"""/-- Nombre de façons de payer `n` avec les pièces de la liste (`f` : réserve de calcul). -/
def faconsAux : Nat → Nat → List Nat → Nat
  | _, 0, _ => 1
  | _, _, [] => 0
  | 0, _, _ => 0
  | f + 1, n + 1, p :: ps => faconsAux f (n + 1) ps + (if p ≤ n + 1 ∧ 0 < p then faconsAux f (n + 1 - p) (p :: ps) else 0)

def facons (n : Nat) (pieces : List Nat) : Nat := faconsAux (2 * n + pieces.length + 1) n pieces

theorem facons_un_euro : facons 100 [1, 2, 5, 10, 20, 50] = 4562 := by -- @exo
  decide +kernel

theorem pieces_1_2 : ∀ n, n < 50 → facons n [1, 2] = n / 2 + 1 := by -- @exo
  decide +kernel""",
["Des calculs : `decide +kernel`.", "La réserve de calcul `f` sert à garantir que le programme s'arrête (chaque appel la fait baisser)."], "Parcours.Combi", requiert="Combinatoire.Menus",
ressources=["[Projet Euler, problème 31 (les pièces anglaises)](https://projecteuler.net/problem=31)"])

exo("Combinatoire", "Partitions", "Les partitions d'un entier", 2, [CD],
"""De combien de façons peut-on écrire 5 comme somme d'entiers, sans tenir compte de l'ordre ?
`5 = 4+1 = 3+2 = 3+1+1 = 2+2+1 = 2+1+1+1 = 1+1+1+1+1` : 7 façons. C'est `p(5)`. Cette suite
grandit très vite : `p(10) = 42`, `p(100) = 190 569 292`. Ramanujan et Hardy ont trouvé une formule
asymptotique étonnante, et Ramanujan a remarqué que `p(5k + 4)` est toujours divisible par 5 !

## À prouver
1. `p_cinq`, `p_dix`, `p_vingt`
2. `ramanujan` : `p(4)`, `p(9)`, `p(14)`, `p(19)`, `p(24)` sont divisibles par 5.""",
"""/-- Nombre de partitions de `n` en parts au plus égales à `k` (`f` : réserve). -/
def partAux : Nat → Nat → Nat → Nat
  | _, 0, _ => 1
  | _, _, 0 => 0
  | 0, _, _ => 0
  | f + 1, n + 1, k + 1 =>
    partAux f (n + 1) k + (if k + 1 ≤ n + 1 then partAux f (n + 1 - (k + 1)) (k + 1) else 0)

def nbPartitions (n : Nat) : Nat := partAux (2 * n + 1) n n

theorem p_cinq : nbPartitions 5 = 7 := by -- @exo
  decide

theorem p_dix : nbPartitions 10 = 42 := by -- @exo
  decide +kernel

theorem p_vingt : nbPartitions 20 = 627 := by -- @exo
  decide +kernel

theorem ramanujan : ∀ k, k < 5 → nbPartitions (5 * k + 4) % 5 = 0 := by -- @exo
  decide +kernel""",
["Des calculs : `decide` / `decide +kernel`."], "Parcours.Combi", requiert="Combinatoire.UnEuro",
ressources=["[Partition d'un entier (Wikipédia)](https://fr.wikipedia.org/wiki/Partition_d%27un_entier)"])

exo("Logique", "Menteur", "Le paradoxe du menteur", 1, ["ParcoursOutils"],
"""Épiménide le Crétois dit : « Tous les Crétois sont menteurs. » Version plus radicale : « Cette
phrase est fausse. » Si elle est vraie, elle est fausse ; si elle est fausse, elle est vraie. En
logique, aucune proposition ne peut être équivalente à sa propre négation.

## À prouver
`menteur : ¬ (P ↔ ¬P)`""",
"""theorem menteur (P : Prop) : ¬ (P ↔ ¬P) := by -- @exo
  intro h
  have hnp : ¬P := fun hp => h.mp hp hp
  exact hnp (h.mpr hnp)""",
["Montre d'abord `¬P` : si `P`, alors `¬P` (par `h.mp`), contradiction.", "Puis `h.mpr` donne `P`."], "Parcours.Logique", requiert="Logique.Equivalence")

exo("Fonctions", "InvolutionsBool", "Les involutions des booléens", 2, ["Solutions.Logique.Bilan"],
"""Une fonction `f` est une **involution** si `f (f x) = x` pour tout `x` (la refaire annule son
effet, comme retourner une crêpe). Sur les booléens, il n'y en a que deux : l'identité et la
négation.

## À prouver
`involutions : (∀ b, f (f b) = b) → f = id ∨ f = not`""",
"""theorem involutions (f : Bool → Bool) (h : ∀ b, f (f b) = b) : f = id ∨ f = not := by -- @exo
  cases ht : f true <;> cases hf : f false
  · have := h true
    rw [ht, hf] at this
    exact absurd this (by decide)
  · right
    funext b
    cases b <;> assumption
  · left
    funext b
    cases b <;> assumption
  · have := h false
    rw [hf, ht] at this
    exact absurd this (by decide)""",
["Quatre cas selon les valeurs de `f true` et `f false` (`cases ht : f true`).", "Pour conclure `f = id`, `funext b` puis `cases b`."], "Parcours.Fonctions", requiert="Fonctions.Involutions")

exo("Algebre", "Klein", "Le groupe de Klein", 1, [LP, RD],
"""Le groupe de Klein a 4 éléments : `(false, false)` (le neutre), et trois autres, chacun étant son
propre inverse. On le réalise avec des couples de booléens et le OU exclusif composante par
composante : c'est le groupe des symétries d'un rectangle (identité, deux réflexions, demi-tour).
Contrairement au groupe des rotations d'un carré, il n'est pas **cyclique** : aucun élément ne
l'engendre à lui seul.

## À prouver
1. `commutatif`, `involutif` : tout élément est son propre inverse.
2. `pas_cyclique` : les puissances de chaque élément ne donnent jamais les 4 éléments.""",
"""abbrev V4 := Bool × Bool

def op (x y : V4) : V4 := (x.1 ^^ y.1, x.2 ^^ y.2)

def elements : List V4 := [(false, false), (false, true), (true, false), (true, true)]

theorem commutatif : ∀ x ∈ elements, ∀ y ∈ elements, op x y = op y x := by -- @exo
  decide

theorem involutif : ∀ x ∈ elements, op x x = (false, false) := by -- @exo
  decide

theorem pas_cyclique : ∀ x ∈ elements, [x, op x x, op x (op x x), op x (op x (op x x))].eraseDups.length < 4 := by -- @exo
  decide""",
["Tout se calcule : `decide`."], "Parcours.Algebre", requiert="Algebre.Triangle",
ressources=["[Groupe de Klein (Wikipédia)](https://fr.wikipedia.org/wiki/Groupe_de_Klein)"])

ecrire_tout()
