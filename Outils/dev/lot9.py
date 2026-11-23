import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fabrique import exo, ecrire_tout

P = "Solutions.Programmes.Definitions"
NS = "Parcours.Prog"

def pr(ident, titre, diff, texte, code, indices, requiert, imports=(P,), ressources=()):
    exo("Programmes", ident, titre, diff, list(imports), texte, code, indices, NS, requiert=requiert, ressources=ressources)

pr("SommePairs", "Deux façons de sommer les pairs", 1,
"""Deux programmes pour additionner les nombres pairs d'une liste : avec une boucle et un `if`,
ou en **filtrant** d'abord puis en sommant. Ils calculent la même chose — prouvons-le.

## À prouver
`deux_versions : sommePairsBoucle l = (l.filter (· % 2 == 0)).sum`""",
"""def sommePairsBoucle : List Nat → Nat
  | [] => 0
  | x :: l => (if x % 2 = 0 then x else 0) + sommePairsBoucle l

theorem deux_versions (l : List Nat) : sommePairsBoucle l = (l.filter (· % 2 == 0)).sum := by -- @exo
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [sommePairsBoucle, List.filter_cons, ih]
    by_cases h : x % 2 = 0 <;> simp [h]""",
["Récurrence ; `List.filter_cons` déplie le filtre.", "Deux cas selon la parité de `x` : `by_cases h : x % 2 = 0 <;> simp [h]`."], "Programmes.Accumulateur")

pr("Popcount", "Compter les bits à 1", 2,
"""Combien de `1` dans l'écriture binaire de `n` ? (Les processeurs ont une instruction exprès,
`popcount`.) On regarde le dernier bit (`n % 2`) et on recommence avec `n / 2`.

## À prouver
1. `bits1_double : bits1 (2 * n) = bits1 n` et `bits1_double_un : bits1 (2 * n + 1) = bits1 n + 1`
2. `bits1_puissance : bits1 (2 ^ k) = 1` (`100…0`)
3. `bits1_mersenne : bits1 (2 ^ k - 1) = k` (`11…1`)""",
"""def bits1 (n : Nat) : Nat := if n = 0 then 0 else n % 2 + bits1 (n / 2)
termination_by n
decreasing_by omega

theorem bits1_zero : bits1 0 = 0 := by -- @exo
  rw [bits1]
  simp

theorem bits1_double (n : Nat) : bits1 (2 * n) = bits1 n := by -- @exo
  by_cases h : n = 0
  · subst h
    simp [bits1_zero]
  · have h' : 2 * n ≠ 0 := by omega
    rw [bits1]
    simp only [h', ↓reduceIte]
    rw [show 2 * n % 2 = 0 by omega, show 2 * n / 2 = n by omega, Nat.zero_add]

theorem bits1_double_un (n : Nat) : bits1 (2 * n + 1) = bits1 n + 1 := by -- @exo
  rw [bits1]
  simp only [show 2 * n + 1 ≠ 0 by omega, ↓reduceIte]
  rw [show (2 * n + 1) % 2 = 1 by omega, show (2 * n + 1) / 2 = n by omega]
  omega

theorem bits1_puissance (k : Nat) : bits1 (2 ^ k) = 1 := by -- @exo
  induction k with
  | zero =>
    rw [Nat.pow_zero, show (1 : Nat) = 2 * 0 + 1 from rfl, bits1_double_un, bits1_zero]
  | succ k ih => rw [Nat.pow_succ, Nat.mul_comm, bits1_double, ih]

theorem bits1_mersenne (k : Nat) : bits1 (2 ^ k - 1) = k := by -- @exo
  induction k with
  | zero => simp [bits1_zero]
  | succ k ih =>
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h : 2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1 := by
      rw [Nat.pow_succ]
      omega
    rw [h, bits1_double_un, ih]""",
["Pour déplier une fonction définie avec `termination_by`, utilise `rw [bits1]` (pas `rfl`).", "Ensuite les deux lemmes `bits1_double` et `bits1_double_un` suffisent pour tout le reste.", "`2^(k+1) − 1 = 2 × (2^k − 1) + 1`."], "Programmes.Chiffres")

pr("PuissanceDeux", "Est-ce une puissance de 2 ?", 2,
"""Pour tester si `n` est une puissance de 2 : on divise par 2 tant que c'est pair, et on regarde
si on arrive à 1.

## À prouver
1. `puissance_ok : estPuissance2 (2 ^ k) = true`
2. `puissance_correct : estPuissance2 n = true → ∃ k, n = 2 ^ k`""",
"""def estPuissance2 (n : Nat) : Bool :=
  if n ≤ 1 then n == 1 else n % 2 == 0 && estPuissance2 (n / 2)
termination_by n
decreasing_by omega

theorem puissance_ok (k : Nat) : estPuissance2 (2 ^ k) = true := by -- @exo
  induction k with
  | zero => rw [estPuissance2]; simp
  | succ k ih =>
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [estPuissance2]
    simp only [show ¬ 2 ^ (k + 1) ≤ 1 by rw [Nat.pow_succ]; omega, ↓reduceIte]
    rw [Nat.pow_succ, Nat.mul_div_cancel _ (by decide), ih]
    simp

theorem puissance_correct (n : Nat) (h : estPuissance2 n = true) : ∃ k, n = 2 ^ k := by -- @exo
  fun_induction estPuissance2 n with
  | case1 n hn =>
    exact ⟨0, by simp at h; omega⟩
  | case2 n hn ih =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨k, hk⟩ := ih h.2
    exact ⟨k + 1, by rw [Nat.pow_succ]; omega⟩""",
["`rw [estPuissance2]` déplie la définition ; puis simplifie le `if`.", "Pour la réciproque : `fun_induction estPuissance2 n`. Dans le cas récursif, `n / 2 = 2^k` et `n` pair donnent `n = 2^(k+1)`."], "Programmes.Popcount")

pr("Crible", "Le crible d'Ératosthène", 2,
"""Pour trouver les nombres premiers jusqu'à 100 (Ératosthène, IIIᵉ siècle av. J.-C.) : écris les
nombres à partir de 2 ; le premier, 2, est premier, raye tous ses multiples ; le suivant non
rayé, 3, est premier, raye ses multiples ; et ainsi de suite.

## À prouver
1. `crible_sous_liste` : le crible ne garde que des nombres de la liste de départ.
2. `vingt_cinq` : il y a 25 nombres premiers inférieurs à 100.
3. `crible_ok` : le crible trouve exactement les nombres qui n'ont pas de diviseur entre 2 et `n − 1`.""",
"""/-- `f` est une réserve de calcul (le nombre d'étapes maximum). -/
def crible : Nat → List Nat → List Nat
  | 0, _ => []
  | _, [] => []
  | f + 1, p :: l => p :: crible f (l.filter (· % p != 0))

def premiersJusqua (n : Nat) : List Nat := crible n (List.range' 2 (n - 2))

theorem crible_sous_liste (f : Nat) (l : List Nat) : ∀ x ∈ crible f l, x ∈ l := by -- @exo
  induction f generalizing l with
  | zero => simp [crible]
  | succ f ih =>
    cases l with
    | nil => simp [crible]
    | cons p l =>
      intro x hx
      simp only [crible, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_filter.mp (ih _ x hx)).1

theorem vingt_cinq : (premiersJusqua 100).length = 25 := by -- @exo
  decide +kernel

theorem crible_ok : premiersJusqua 100 = (List.range 100).filter fun n =>
    2 ≤ n && (List.range n).all fun d => d < 2 || n % d != 0 := by -- @exo
  decide +kernel""",
["`crible_sous_liste` : récurrence sur la réserve `f`, en généralisant la liste ; `List.mem_filter`.", "Les deux autres sont des calculs : `decide +kernel`."], "Programmes.Recherche",
ressources=["[Crible d'Ératosthène (Wikipédia)](https://fr.wikipedia.org/wiki/Crible_d%27%C3%89ratosth%C3%A8ne)"])

pr("Romains", "Les chiffres romains", 2,
"""`MMXXIV` = 2024. Écrire en chiffres romains se fait de façon **gloutonne** avec les briques
`M = 1000, CM = 900, D = 500, CD = 400, C = 100, XC = 90, L, XL, X, IX, V, IV, I`. Le programme
`romain` est donné.

**À toi d'écrire la lecture** `lire` : un chiffre suivi d'un chiffre **plus grand** se soustrait
(`IX = 9`), sinon il s'ajoute (`XI = 11`).

## À faire
1. Écris `lire` ;
2. prouve `exemples_romains` et `aller_retour_romain : n < 4000 → lire (romain n) = n`. (Pour que le noyau de
   Lean ne s'essouffle pas, on vérifie d'abord les nombres par paquets de 100.)""",
"""inductive Chiffre where
  | I | V | X | L | C | D | M
  deriving DecidableEq

def Chiffre.val : Chiffre → Nat
  | .I => 1 | .V => 5 | .X => 10 | .L => 50 | .C => 100 | .D => 500 | .M => 1000

open Chiffre in
def briques : List (Nat × List Chiffre) :=
  [(1000, [M]), (900, [C, M]), (500, [D]), (400, [C, D]), (100, [C]), (90, [X, C]), (50, [L]),
   (40, [X, L]), (10, [X]), (9, [I, X]), (5, [V]), (4, [I, V]), (1, [I])]

/-- `f` est une réserve de calcul. -/
def ecrire : Nat → List (Nat × List Chiffre) → Nat → List Chiffre
  | 0, _, _ => []
  | _, [], _ => []
  | f + 1, (v, s) :: r, n => if v ≤ n then s ++ ecrire f ((v, s) :: r) (n - v) else ecrire f r n

def romain (n : Nat) : List Chiffre := ecrire 30 briques n

def lire : List Chiffre → Nat -- @exo
  | [] => 0
  | [a] => a.val
  | a :: b :: r => if a.val < b.val then lire (b :: r) - a.val else a.val + lire (b :: r)

open Chiffre in
theorem exemples_romains : romain 2024 = [M, M, X, X, I, V] ∧ romain 1789 = [M, D, C, C, L, X, X, X, I, X] ∧
    lire [M, C, M, X, C] = 1990 := by -- @exo
  decide

theorem par_centaines : ∀ k, k < 40 → ∀ j, j < 100 → lire (romain (100 * k + j)) = 100 * k + j := by -- @exo
  decide +kernel

theorem aller_retour_romain (n : Nat) (h : n < 4000) : lire (romain n) = n := by -- @exo
  have := par_centaines (n / 100) (by omega) (n % 100) (Nat.mod_lt _ (by decide))
  rwa [Nat.div_add_mod] at this""",
["`lire` se définit par cas : liste vide, un seul chiffre, ou deux chiffres `a :: b :: r` (on compare `a.val` et `b.val`).", "Attention : dans `IX`, on calcule `lire [X] − 1`.", "Les preuves sont des calculs : `decide +kernel` vérifie les 4000 nombres."], "Programmes.Bases",
ressources=["[Numération romaine (Wikipédia)](https://fr.wikipedia.org/wiki/Num%C3%A9ration_romaine)"])

pr("Morse", "Le code Morse", 2,
"""Le code Morse (1838) code chaque lettre par des points et des traits : `E = ·`, `T = −`,
`S = · · ·`, `O = − − −`. Les lettres fréquentes ont des codes courts.

Attention : sans les espaces entre lettres, on ne peut pas décoder ! `E E = · · = I`.

On code les lettres par des nombres (`A = 0`, …, `Z = 25`) et `false = ·`, `true = −`.

## À prouver
1. `lettre_morse` : chaque lettre se décode correctement.
2. `decoder_coder` : un mot codé lettre par lettre se décode en le mot de départ.
3. `ambigu : morse 4 ++ morse 4 = morse 8` (« EE » collés = « I »).""",
"""def tableMorse : List (List Bool) :=
  [[false, true], [true, false, false, false], [true, false, true, false], [true, false, false],
   [false], [false, false, true, false], [true, true, false], [false, false, false, false],
   [false, false], [false, true, true, true], [true, false, true], [false, true, false, false],
   [true, true], [true, false], [true, true, true], [false, true, true, false],
   [true, true, false, true], [false, true, false], [false, false, false], [true],
   [false, false, true], [false, false, false, true], [false, true, true], [true, false, false, true],
   [true, false, true, true], [true, true, false, false]]

def morse (c : Nat) : List Bool := tableMorse.getD c []

def lettre (code : List Bool) : Option Nat := (List.range 26).find? fun c => morse c == code

def decoder : List (List Bool) → Option (List Nat)
  | [] => some []
  | x :: r =>
    match lettre x, decoder r with
    | some c, some w => some (c :: w)
    | _, _ => none

theorem lettre_morse : ∀ c, c < 26 → lettre (morse c) = some c := by -- @exo
  decide

theorem decoder_coder (w : List Nat) (h : ∀ c ∈ w, c < 26) : decoder (w.map morse) = some w := by -- @exo
  induction w with
  | nil => rfl
  | cons c w ih =>
    simp only [List.map_cons, decoder, lettre_morse c (h c List.mem_cons_self),
      ih (fun d hd => h d (List.mem_cons_of_mem c hd))]

theorem ambigu : morse 4 ++ morse 4 = morse 8 := by -- @exo
  decide""",
["`lettre_morse` : 26 cas, `decide`.", "`decoder_coder` : récurrence sur le mot ; utilise `lettre_morse` pour la première lettre et l'hypothèse de récurrence pour la suite."], "Programmes.Cesar",
ressources=["[Code Morse international (Wikipédia)](https://fr.wikipedia.org/wiki/Code_Morse_international)"])

pr("Mastermind", "Mastermind", 1,
"""Au Mastermind, un joueur cache une combinaison de 4 couleurs (parmi 6) ; l'autre propose des
combinaisons et reçoit deux indices : le nombre de pions **bien placés**, et le nombre de pions
de la bonne couleur mais **mal placés**.

## À prouver
1. `exemple_mastermind` : pour le secret `[1, 2, 3, 4]` et la proposition `[1, 3, 2, 5]` : 1 bien placé, 2 mal placés.
2. `bienPlaces_le` : il y a au plus autant de bien placés que de pions.
3. `bienPlaces_comm` : l'indice « bien placés » est symétrique.""",
"""def bienPlaces (s g : List Nat) : Nat := (List.zipWith (· == ·) s g).count true

def communs (s g : List Nat) : Nat := ((List.range 6).map fun c => min (s.count c) (g.count c)).sum

def malPlaces (s g : List Nat) : Nat := communs s g - bienPlaces s g

theorem exemple_mastermind : bienPlaces [1, 2, 3, 4] [1, 3, 2, 5] = 1 ∧ malPlaces [1, 2, 3, 4] [1, 3, 2, 5] = 2 := by -- @exo
  decide

theorem bienPlaces_le (s g : List Nat) : bienPlaces s g ≤ s.length := by -- @exo
  unfold bienPlaces
  have h1 := List.count_le_length (a := true) (l := List.zipWith (· == ·) s g)
  rw [List.length_zipWith] at h1
  omega

theorem bienPlaces_comm (s g : List Nat) : bienPlaces s g = bienPlaces g s := by -- @exo
  unfold bienPlaces
  rw [List.zipWith_comm]
  congr 2
  funext a b
  exact Bool.beq_comm""",
["`exemple` : `decide`.", "`bienPlaces_le` : `List.count_le_length` et `List.length_zipWith` (la longueur est le minimum des deux).", "`bienPlaces_comm` : `List.zipWith_comm` échange les deux listes."], "Programmes.Compter",
ressources=["[Mastermind (Wikipédia)](https://fr.wikipedia.org/wiki/Mastermind)"])

pr("ISBN", "La clé ISBN", 3,
"""Le numéro ISBN-10 d'un livre a une clé de contrôle : `10 d₁ + 9 d₂ + ⋯ + 1 d₁₀` doit être
multiple de 11. Elle détecte non seulement une faute de frappe, mais aussi l'**inversion de deux
chiffres voisins** (l'erreur la plus courante quand on recopie un numéro) : échanger `a` et `b`
change la somme de `a − b`, qui n'est jamais multiple de 11 si `a ≠ b`.

## À prouver
1. `exemple_isbn` : `0-306-40615-2` est un ISBN valide (c'est l'exemple de Wikipédia).
2. `isbnSomme_append` : la somme d'une concaténation.
3. `inversion` : échanger deux chiffres voisins différents change la clé.""",
"""def isbnSomme : List Nat → Nat
  | [] => 0
  | d :: r => (r.length + 1) * d + isbnSomme r

/-- La contribution de `l` quand on lui ajoute `k` chiffres à droite. -/
def poids : List Nat → Nat → Nat
  | [], _ => 0
  | d :: r, k => (r.length + k + 1) * d + poids r k

def isbnValide (l : List Nat) : Bool := l.length == 10 && isbnSomme l % 11 == 0

theorem exemple_isbn : isbnValide [0, 3, 0, 6, 4, 0, 6, 1, 5, 2] = true := by -- @exo
  decide

theorem isbnSomme_append (l x : List Nat) : isbnSomme (l ++ x) = isbnSomme x + poids l x.length := by -- @exo
  induction l with
  | nil => simp [poids]
  | cons d l ih =>
    simp only [List.cons_append, isbnSomme, poids, ih, List.length_append]
    rw [show l.length + x.length + 1 = l.length + x.length + 1 from rfl]
    omega

theorem inversion (l₁ l₂ : List Nat) (a b : Nat) (ha : a < 10) (hb : b < 10)
    (h : isbnSomme (l₁ ++ a :: b :: l₂) % 11 = isbnSomme (l₁ ++ b :: a :: l₂) % 11) : a = b := by -- @exo
  rw [isbnSomme_append, isbnSomme_append] at h
  simp only [isbnSomme, List.length_cons, Nat.add_mul, Nat.one_mul] at h
  omega""",
["`isbnSomme_append` : récurrence sur `l`.", "Pour `inversion`, après `isbnSomme_append`, les contributions de `l₁` sont les mêmes des deux côtés (les longueurs sont égales). Développe `(L + 2) * a` avec `Nat.add_mul`, puis `omega`."], "Programmes.Luhn",
ressources=["[International Standard Book Number (Wikipédia)](https://fr.wikipedia.org/wiki/International_Standard_Book_Number)"])

pr("RecordSyracuse", "Le vol record de Syracuse", 1,
"""La suite de Syracuse (si `n` est pair, `n / 2`, sinon `3n + 1`) finit toujours par atteindre 1,
du moins pour tous les nombres qu'on a testés. Le « temps de vol » de 27 est spectaculaire :
111 étapes, en montant jusqu'à 9232, alors que ses voisins atterrissent en quelques étapes.

## À prouver
1. `vol_27` : 111 étapes et une altitude maximale de 9232.
2. `record_vol` : pourtant, sous 100, le record de durée est détenu par 97 (118 étapes) ;
3. `record_altitude` : et aucun nombre inférieur à 100 ne monte plus haut que 9232.""",
"""def pasSyracuse (n : Nat) : Nat := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Nombre d'étapes pour atteindre 1 (`f` : réserve de calcul). -/
def vol : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, n => if n ≤ 1 then 0 else 1 + vol f (pasSyracuse n)

def altitude : Nat → Nat → Nat
  | 0, n => n
  | f + 1, n => if n ≤ 1 then n else max n (altitude f (pasSyracuse n))

theorem vol_27 : vol 200 27 = 111 ∧ altitude 200 27 = 9232 := by -- @exo
  decide +kernel

theorem record_vol : vol 200 97 = 118 ∧ ∀ n, n < 100 → vol 200 n ≤ vol 200 97 := by -- @exo
  decide +kernel

theorem record_altitude : ∀ n, n < 100 → altitude 200 n ≤ 9232 := by -- @exo
  decide +kernel""",
["Des calculs : `decide` ou `decide +kernel`."], "Programmes.FizzBuzz",
ressources=["[Conjecture de Syracuse (Wikipédia)](https://fr.wikipedia.org/wiki/Conjecture_de_Syracuse)"])

pr("RegarderDire", "La suite de Conway", 1,
"""`1 → 11 → 21 → 1211 → 111221 → 312211 → …` : chaque terme **décrit** le précédent à voix haute
(« un 1 », « deux 1 », « un 2, un 1 »…). John Conway a prouvé que la longueur croît d'environ 30 %
à chaque étape, et qu'aucun chiffre plus grand que 3 n'apparaît jamais.

## À prouver
1. `conway : repeter regarder 5 [1] = [3, 1, 2, 2, 1, 1]`
2. `deux_deux : regarder [2, 2] = [2, 2]` (« deux 2 » : un point fixe !)
3. `longueur_paire : (regarder l).length = 2 * (grouper l).length`
4. `pas_de_quatre` : dans les 12 premiers termes, aucun chiffre ne dépasse 3.""",
"""def grouper : List Nat → List (Nat × Nat)
  | [] => []
  | x :: l =>
    match grouper l with
    | (k, y) :: r => if x = y then (k + 1, y) :: r else (1, x) :: (k, y) :: r
    | [] => [(1, x)]

def regarder (l : List Nat) : List Nat := (grouper l).flatMap fun p => [p.1, p.2]

theorem conway : repeter regarder 5 [1] = [3, 1, 2, 2, 1, 1] := by -- @exo
  decide

theorem deux_deux : regarder [2, 2] = [2, 2] := by -- @exo
  decide

theorem longueur_paire (l : List Nat) : (regarder l).length = 2 * (grouper l).length := by -- @exo
  simp only [regarder, List.length_flatMap, List.length_cons, List.length_nil]
  rw [List.map_const', List.sum_replicate_nat, Nat.mul_comm]

theorem pas_de_quatre : ∀ k, k < 12 → ∀ d ∈ repeter regarder k [1], d ≤ 3 := by -- @exo
  decide +kernel""",
["Les calculs : `decide` / `decide +kernel`.", "`longueur_paire` : chaque groupe donne 2 chiffres ; `List.length_flatMap`, puis `List.map_const'` et `List.sum_replicate_nat`."], "Programmes.Magicien",
ressources=["[Suite de Conway (Wikipédia)](https://fr.wikipedia.org/wiki/Suite_de_Conway)"])

pr("Pisano", "Le dernier chiffre des Fibonacci", 3,
"""Les derniers chiffres des nombres de Fibonacci : `0, 1, 1, 2, 3, 5, 8, 3, 1, 4, 5, 9, 4, …` Ils se
répètent avec une période de **60** (la période de Pisano pour 10). Pourquoi périodique ? Le
dernier chiffre de `F(n+2)` ne dépend que de ceux de `F(n)` et `F(n+1)` : on se promène dans les
100 couples possibles, et on finit forcément par repasser par un couple déjà vu.

## À prouver
1. `pisano : repeter pasFib 60 (0, 1) = (0, 1)` et `pas_avant_60` : pas avant 60.
2. `repeter_add`, `repeter_succ'` : propriétés de `repeter`.
3. `etat_fib : repeter pasFib n (0, 1) = (fib n % 10, fib (n + 1) % 10)`
4. `dernier_chiffre_fib : fib (n + 60) % 10 = fib n % 10`""",
"""open Parcours.Recurrence

def pasFib (p : Nat × Nat) : Nat × Nat := (p.2, (p.1 + p.2) % 10)

theorem pisano : repeter pasFib 60 (0, 1) = (0, 1) := by -- @exo
  decide

theorem pas_avant_60 : ∀ k, k < 59 → repeter pasFib (k + 1) (0, 1) ≠ (0, 1) := by -- @exo
  decide +kernel

theorem repeter_add {α : Type} (f : α → α) (m n : Nat) (x : α) :
    repeter f (m + n) x = repeter f m (repeter f n x) := by -- @exo
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [← Nat.add_assoc]
    exact ih (f x)

theorem repeter_succ' {α : Type} (f : α → α) (n : Nat) (x : α) :
    repeter f (n + 1) x = f (repeter f n x) := by -- @exo
  rw [Nat.add_comm, repeter_add]
  rfl

theorem etat_fib (n : Nat) : repeter pasFib n (0, 1) = (fib n % 10, fib (n + 1) % 10) := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [repeter_succ', ih]
    simp only [pasFib, Prod.mk.injEq, true_and]
    rw [show n + 1 + 1 = n + 2 from rfl, fib_add_two]
    omega

theorem dernier_chiffre_fib (n : Nat) : fib (n + 60) % 10 = fib n % 10 := by -- @exo
  have h := etat_fib (n + 60)
  rw [repeter_add, pisano, etat_fib] at h
  exact (congrArg Prod.fst h).symm""",
["`repeter_add` : récurrence sur `n` en généralisant `x`.", "`etat_fib` : récurrence ; `fib (n + 2) = fib n + fib (n + 1)` et `Nat.add_mod`.", "Pour conclure : `repeter pasFib (n + 60) = repeter pasFib n ∘ repeter pasFib 60`."], "Programmes.Kaprekar",
ressources=["[Période de Pisano (Wikipédia)](https://fr.wikipedia.org/wiki/P%C3%A9riode_de_Pisano)"])

# --- Tris : tri par sélection
exo("Tris", "TriSelection", "Le tri par sélection", 3, ["Solutions.Tris.Definitions"],
"""Le tri par sélection : on cherche le **plus petit** élément, on le met en tête, et on recommence
avec le reste. C'est le tri que l'on fait naturellement avec des cartes à jouer étalées sur une
table.

## À prouver
1. `minL_le` : le minimum est plus petit que tout le monde ; `minL_mem` : c'est l'un des éléments.
2. `triSelection_perm : (triSelection l).Perm l`
3. `triSelection_trie : Trie (triSelection l)`""",
"""def minL : Nat → List Nat → Nat
  | m, [] => m
  | m, x :: l => minL (min m x) l

theorem minL_le (m : Nat) (l : List Nat) : minL m l ≤ m ∧ ∀ y ∈ l, minL m l ≤ y := by -- @exo
  induction l generalizing m with
  | nil =>
    refine ⟨Nat.le_refl m, fun y hy => ?_⟩
    simp at hy
  | cons x l ih =>
    simp only [minL, List.mem_cons]
    obtain ⟨h1, h2⟩ := ih (min m x)
    refine ⟨by omega, fun y hy => ?_⟩
    rcases hy with rfl | hy
    · omega
    · exact h2 y hy

theorem minL_mem (m : Nat) (l : List Nat) : minL m l ∈ m :: l := by -- @exo
  induction l generalizing m with
  | nil => simp [minL]
  | cons x l ih =>
    simp only [minL]
    have := ih (min m x)
    simp only [List.mem_cons] at this ⊢
    rcases this with h | h
    · rcases Nat.le_total m x with hm | hm
      · left; rw [h, Nat.min_eq_left hm]
      · right; left; rw [h, Nat.min_eq_right hm]
    · right; right; exact h

def triSelection (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | x :: r => minL x r :: triSelection ((x :: r).erase (minL x r))
termination_by l.length
decreasing_by
  rw [List.length_erase_of_mem (minL_mem x r)]
  simp

theorem triSelection_perm (l : List Nat) : (triSelection l).Perm l := by -- @exo
  fun_induction triSelection l with
  | case1 => exact List.Perm.refl _
  | case2 x r ih =>
    exact ((ih.cons _).trans (List.perm_cons_erase (minL_mem x r)).symm)

theorem triSelection_trie (l : List Nat) : Trie (triSelection l) := by -- @exo
  fun_induction triSelection l with
  | case1 => exact trie_nil
  | case2 x r ih =>
    rw [trie_cons]
    refine ⟨fun y hy => ?_, ih⟩
    have hy' := (triSelection_perm _).mem_iff.mp hy
    have hy'' := List.mem_of_mem_erase hy'
    obtain ⟨h1, h2⟩ := minL_le x r
    rcases List.mem_cons.mp hy'' with rfl | h
    · exact h1
    · exact h2 y h""",
["`minL_le` et `minL_mem` : récurrence sur `l` en généralisant `m`.", "`List.perm_cons_erase : a ∈ l → l ~ a :: l.erase a`.", "Pour `triSelection_trie` : un élément du reste est dans `l.erase m`, donc dans `l` (`List.mem_of_mem_erase`), donc plus grand que `m`."], "Parcours.Tris", requiert="Tris.TriInsertion",
ressources=["[Tri par sélection (Wikipédia)](https://fr.wikipedia.org/wiki/Tri_par_s%C3%A9lection)"])

ecrire_tout()
