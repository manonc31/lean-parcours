import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fabrique import exo, ecrire_tout

AR = "Solutions.Arithmetique.Definitions"
NSO = "Parcours.Olymp"
# ------------------------------------------------------------ Olympiades
exo("Olympiades", "Cinquieme", "La puissance cinquième", 2, [AR],
 """Pour tout entier `n`, `n⁵` et `n` ont le même dernier chiffre ! (Essaie : `2⁵ = 32`, `3⁵ = 243`, `7⁵ = 16807`.)
Ici, la version modulo 5 (c'est le petit théorème de Fermat pour `p = 5`).

## À prouver
`cinquieme (n : Nat) : (n * n * n * n * n) % 5 = n % 5`""",
 """theorem cinquieme (n : Nat) : (n * n * n * n * n) % 5 = n % 5 := by -- @exo
  have : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  rcases this with h | h | h | h | h <;> simp [Nat.mul_mod, h]""",
 ["Raisonne sur le reste de `n` modulo 5 : cinq cas (`omega` fournit la disjonction).", "Dans chaque cas : `simp [Nat.mul_mod, h]`."], NSO, requiert="Olympiades.Parite")
exo("Olympiades", "Sept", "Sept divise 2³ⁿ − 1", 2, [AR],
 """`2³ⁿ = 8ⁿ`, et `8 = 7 + 1`… donc `8ⁿ` laisse le reste 1 dans la division par 7.

## À prouver
`sept (n : Nat) : (2 ^ (3 * n)) % 7 = 1`""",
 """theorem sept (n : Nat) : (2 ^ (3 * n)) % 7 = 1 := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 3 * (n + 1) = 3 * n + 3 by omega, Nat.pow_add, Nat.mul_mod, ih]""",
 ["Récurrence sur `n`.", "`2 ^ (3 * (n + 1)) = 2 ^ (3 * n) * 2 ^ 3` (`Nat.pow_add`), puis `Nat.mul_mod` et `ih`."], NSO, requiert="Olympiades.Cinquieme")
exo("Olympiades", "IMO1964", "IMO 1964, problème 1", 3, [AR],
 """> Trouver tous les entiers `n` tels que `2ⁿ − 1` est divisible par 7.

Réponse : exactement les multiples de 3. La suite des restes de `2ⁿ` modulo 7 est périodique :
`1, 2, 4, 1, 2, 4, …`

## À prouver
1. `reste_puissance_deux : 2 ^ n % 7 = (si n % 3 = 0 alors 1 sinon si n % 3 = 1 alors 2 sinon 4)`
2. `imo1964 (n : Nat) : (2 ^ n - 1) % 7 = 0 ↔ n % 3 = 0`""",
 """theorem reste_puissance_deux (n : Nat) :
    2 ^ n % 7 = if n % 3 = 0 then 1 else if n % 3 = 1 then 2 else 4 := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih]
    repeat' split
    all_goals omega

theorem imo1964 (n : Nat) : (2 ^ n - 1) % 7 = 0 ↔ n % 3 = 0 := by -- @exo
  have h := reste_puissance_deux n
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  repeat' split at h
  all_goals omega""",
 ["Pour le lemme : récurrence, `Nat.pow_succ` et `Nat.mul_mod`, puis découpe tous les `if` avec `repeat' split` et conclus avec `all_goals omega`.",
  "Pour le théorème : `2 ^ n ≥ 1` (`Nat.one_le_two_pow`) ; découpe les cas du lemme avec `repeat' split at h`, puis `omega` dans chacun (`all_goals omega`)."], NSO, requiert="Olympiades.Sept")
exo("Olympiades", "DifferenceCarres", "Deux carrés qui diffèrent de 2", 2, [AR],
 """Deux carrés parfaits ne diffèrent **jamais** de 2. L'astuce : regarder modulo 4. Un carré vaut
toujours 0 ou 1 modulo 4.

## À prouver
`difference_carres : ¬∃ x y : Nat, x * x = y * y + 2`""",
 """theorem difference_carres : ¬∃ x y : Nat, x * x = y * y + 2 := by -- @exo
  rintro ⟨x, y, h⟩
  have carre : ∀ z : Nat, z * z % 4 = 0 ∨ z * z % 4 = 1 := by
    intro z
    have : z % 4 = 0 ∨ z % 4 = 1 ∨ z % 4 = 2 ∨ z % 4 = 3 := by omega
    rcases this with hz | hz | hz | hz <;> simp [Nat.mul_mod, hz]
  have hx := carre x
  have hy := carre y
  omega""",
 ["Lemme : pour tout `z`, `z * z % 4` vaut 0 ou 1 (quatre cas sur `z % 4`, `Nat.mul_mod`).", "Applique-le à `x` et `y`, puis `omega` avec `h`."], NSO, requiert="Olympiades.Parite")
exo("Olympiades", "SommeCubes", "Somme de trois cubes", 2, [AR],
 """Si `a + b + c = 0`, alors `a³ + b³ + c³ = 3abc`. Une identité qui sert souvent en compétition
(par exemple pour factoriser).

## À prouver
`somme_cubes (a b c : Int) (h : a + b + c = 0) : a ^ 3 + b ^ 3 + c ^ 3 = 3 * a * b * c`""",
 """theorem somme_cubes (a b c : Int) (h : a + b + c = 0) : a ^ 3 + b ^ 3 + c ^ 3 = 3 * a * b * c := by -- @exo
  have hc : c = -a - b := by omega
  subst hc
  grind""",
 ["Exprime `c` en fonction de `a` et `b` (`omega`), puis `subst`.", "Il reste une identité polynomiale : `grind`."], NSO, requiert="Olympiades.QuatreConsecutifs")
exo("Olympiades", "EntreDeuxCarres", "Rien entre deux carrés consécutifs", 2, [AR],
 """Il n'y a aucun carré parfait strictement entre `n²` et `(n + 1)²`.

## À prouver
`entre_deux_carres : ¬∃ m, n * n < m * m ∧ m * m < (n + 1) * (n + 1)`""",
 """theorem entre_deux_carres (n : Nat) : ¬∃ m, n * n < m * m ∧ m * m < (n + 1) * (n + 1) := by -- @exo
  rintro ⟨m, h1, h2⟩
  rcases Nat.lt_or_ge n m with h | h
  · have : (n + 1) * (n + 1) ≤ m * m := Nat.mul_le_mul h h
    omega
  · have : m * m ≤ n * n := Nat.mul_le_mul h h
    omega""",
 ["Compare `m` et `n` (`Nat.lt_or_ge n m`).", "Si `n < m`, alors `n + 1 ≤ m` donc `(n+1)² ≤ m²` (`Nat.mul_le_mul`). Sinon `m² ≤ n²`."], NSO, requiert="Olympiades.Parite")
exo("Olympiades", "Onze", "Onze divise 10²ⁿ⁺¹ + 1", 3, [AR],
 """`11`, `1001 = 7 × 11 × 13`, `100001 = 11 × 9091`… Les nombres `10^(2n+1) + 1` sont tous divisibles par 11.
(Critère de divisibilité par 11 : `10 ≡ −1` modulo 11.)

## À prouver
`onze (n : Nat) : (10 ^ (2 * n + 1) + 1) % 11 = 0`""",
 """theorem onze (n : Nat) : (10 ^ (2 * n + 1) + 1) % 11 = 0 := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, Nat.pow_add]
    have : (10 : Nat) ^ 2 = 100 := rfl
    rw [this]
    omega""",
 ["Récurrence. `10 ^ (2(n+1)+1) = 10 ^ (2n+1) * 100`.", "Comme `100 = 99 + 1` et `99 = 9 × 11`, `omega` sait conclure à partir de l'hypothèse de récurrence."], NSO, requiert="Olympiades.Sept")

# ------------------------------------------------------------ Matrices
MD = "Solutions.Matrices.Definitions"
NSM = "Parcours.Matrices"
exo("Matrices", "Associativite", "Le produit est associatif", 2, [MD],
 """Le produit de matrices est **associatif** : `(AB)C = A(BC)`. (Mais pas commutatif, voir l'exercice suivant !)

## À prouver
1. `mul_assoc : A * B * C = A * (B * C)`
2. `id_mul : id2 * A = A` et `mul_id : A * id2 = A`""",
 """theorem mul_assoc (A B C : M2) : A * B * C = A * (B * C) := by -- @exo
  obtain ⟨a, b, c, d⟩ := A
  obtain ⟨e, f, g, h⟩ := B
  obtain ⟨i, j, k, l⟩ := C
  simp only [M2.mul_def, M2.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

theorem id_mul (A : M2) : M2.id2 * A = A := by -- @exo
  obtain ⟨a, b, c, d⟩ := A
  simp only [M2.mul_def, M2.id2, M2.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

theorem mul_id (A : M2) : A * M2.id2 = A := by -- @exo
  obtain ⟨a, b, c, d⟩ := A
  simp only [M2.mul_def, M2.id2, M2.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind""",
 ["`obtain ⟨a, b, c, d⟩ := A` (idem pour `B`, `C`) fait apparaître les coefficients.", "`simp only [M2.mul_def, M2.mk.injEq]` transforme l'égalité de matrices en 4 égalités d'entiers ; `refine ⟨?_, ?_, ?_, ?_⟩ <;> grind`."], NSM)
exo("Matrices", "NonCommutatif", "Le produit n'est pas commutatif", 1, [MD],
 """Contrairement aux nombres, `AB ≠ BA` en général ! Trouve deux matrices qui ne commutent pas.

## À prouver
`non_commutatif : ∃ A B : M2, A * B ≠ B * A`""",
 """theorem non_commutatif : ∃ A B : M2, A * B ≠ B * A := by -- @exo
  exact ⟨⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, by decide⟩""",
 ["Essaie `A = ⎛0 1⎞` et `B = ⎛0 0⎞` (en Lean : `⟨0, 1, 0, 0⟩` et `⟨0, 0, 1, 0⟩`).", "Une fois les matrices données, `decide` vérifie `A * B ≠ B * A`."], NSM, requiert="Matrices.Associativite")
exo("Matrices", "Determinant", "Le déterminant d'un produit", 2, [MD],
 """Le déterminant est **multiplicatif** : `det(AB) = det(A) det(B)`. Géométriquement : le déterminant
mesure comment une matrice multiplie les aires, et faire deux transformations multiplie les facteurs.

## À prouver
1. `det_mul : det (A * B) = det A * det B`
2. `det_id : det id2 = 1`""",
 """theorem det_mul (A B : M2) : M2.det (A * B) = M2.det A * M2.det B := by -- @exo
  obtain ⟨a, b, c, d⟩ := A
  obtain ⟨e, f, g, h⟩ := B
  simp only [M2.det, M2.mul_def]
  grind

theorem det_id : M2.det M2.id2 = 1 := by -- @exo
  rfl""",
 ["Déplie tout : `simp only [M2.det, M2.mul_def]`, puis `grind`."], NSM, requiert="Matrices.Associativite")
exo("Matrices", "Inverse", "L'inverse d'une matrice", 3, [MD],
 """La matrice « adjointe » de `⎛a b⎞ / ⎝c d⎠` est `⎛d −b⎞ / ⎝−c a⎠`. Leur produit vaut `det × id`.
Donc une matrice de déterminant 1 est inversible, d'inverse son adjointe.

## À prouver
1. `mul_adj : A * adj A = ⟨det A, 0, 0, det A⟩`
2. `inverse : det A = 1 → A * adj A = id2 ∧ adj A * A = id2`""",
 """def adj (A : M2) : M2 := ⟨A.d, -A.b, -A.c, A.a⟩

theorem mul_adj (A : M2) : A * adj A = ⟨M2.det A, 0, 0, M2.det A⟩ := by -- @exo
  obtain ⟨a, b, c, d⟩ := A
  simp only [adj, M2.det, M2.mul_def, M2.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

theorem inverse (A : M2) (h : M2.det A = 1) : A * adj A = M2.id2 ∧ adj A * A = M2.id2 := by -- @exo
  obtain ⟨a, b, c, d⟩ := A
  simp only [M2.det] at h
  simp only [adj, M2.mul_def, M2.id2, M2.mk.injEq]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;> grind""",
 ["Comme d'habitude : coefficients, `simp only [adj, M2.det, M2.mul_def, M2.mk.injEq]`, `refine ⟨?_, ?_, ?_, ?_⟩ <;> grind`.", "Pour `inverse`, n'oublie pas de déplier `det` dans l'hypothèse `h` (`simp only [M2.det] at h`)."], NSM, requiert="Matrices.Determinant")
exo("Matrices", "Fibonacci", "Fibonacci par les matrices", 3, [MD],
 """La matrice `F = ⎛1 1⎞ / ⎝1 0⎠` « fabrique » Fibonacci :
`Fⁿ⁺¹ = ⎛F(n+2)  F(n+1)⎞ / ⎝F(n+1)  F(n)⎠`.
Avec l'exponentiation rapide de matrices, on calcule `F(n)` en `log n` étapes : le millionième
nombre de Fibonacci (208 988 chiffres !) se calcule en une fraction de seconde.

## À prouver
`puissance_fib (n : Nat) : M2.puiss F (n + 1) = ⟨fib (n + 2), fib (n + 1), fib (n + 1), fib n⟩`
(les `fib` sont convertis en `Int`)""",
 """open Parcours.Recurrence

def F : M2 := ⟨1, 1, 1, 0⟩

theorem puissance_fib (n : Nat) :
    M2.puiss F (n + 1) = ⟨(fib (n + 2) : Int), fib (n + 1), fib (n + 1), fib n⟩ := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show M2.puiss F (n + 1 + 1) = M2.puiss F (n + 1) * F from rfl, ih]
    simp only [M2.mul_def, F, M2.mk.injEq]
    rw [show n + 1 + 2 = (n + 1) + 2 from rfl, fib_add_two (n + 1), fib_add_two n]
    simp only [Int.natCast_add]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> grind""",
 ["Récurrence sur `n`. `M2.puiss F (n + 2) = M2.puiss F (n + 1) * F` par définition (`rfl`).", "Après `simp only [M2.mul_def, F, M2.mk.injEq]`, utilise `fib_add_two` pour faire apparaître les sommes, et `Int.natCast_add` pour les conversions, puis `grind`."], NSM, requiert="Matrices.Associativite, Recurrence.Fibonacci")
exo("Matrices", "DetPuissance", "Déterminant d'une puissance", 2, ["Solutions.Matrices.Determinant"],
 """`det(Aⁿ) = (det A)ⁿ`. Appliqué à la matrice de Fibonacci (de déterminant −1), on retrouve
l'identité de Cassini !

## À prouver
`det_puiss (A : M2) (n : Nat) : M2.det (M2.puiss A n) = M2.det A ^ n`""",
 """theorem det_puiss (A : M2) (n : Nat) : M2.det (M2.puiss A n) = M2.det A ^ n := by -- @exo
  induction n with
  | zero =>
    rw [Int.pow_zero]
    rfl
  | succ n ih =>
    rw [show M2.puiss A (n + 1) = M2.puiss A n * A from rfl, det_mul, ih, Int.pow_succ]""",
 ["Récurrence sur `n`, avec `det_mul` et `Int.pow_succ`."], NSM)

# ------------------------------------------------------------ Récurrence
RD = "Solutions.Recurrence.Definitions"
NSR = "Parcours.Recurrence"
exo("Recurrence", "SommeFactorielles", "Une somme de factorielles", 3, [RD],
 """`0·0! + 1·1! + 2·2! + ⋯ + n·n! = (n+1)! − 1`. (Joli : `1 + 4 + 18 = 23 = 4! − 1`.)

## À prouver
`somme_factorielles (n : Nat) : somme (fun k => k * fact k) (n + 1) + 1 = fact (n + 1)`""",
 """theorem somme_factorielles (n : Nat) : somme (fun k => k * fact k) (n + 1) + 1 = fact (n + 1) := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ, fact_succ (n + 1)]
    grind""",
 ["Récurrence ; `somme_succ` et `fact_succ`.", "`(n+2)! = (n+2)(n+1)! = (n+1)(n+1)! + (n+1)!` : `grind` avec l'hypothèse de récurrence."], NSR, requiert="Recurrence.Croissance")
exo("Recurrence", "CarreEtPuissance", "n² contre 2ⁿ", 3, [RD],
 """Pour `n ≥ 4`, `n² ≤ 2ⁿ` : l'exponentielle finit toujours par battre le polynôme.
(Faux pour `n = 3` : `9 > 8`.)

## À prouver
`carre_le_puissance (n : Nat) (h : 4 ≤ n) : n ^ 2 ≤ 2 ^ n`""",
 """theorem carre_le_puissance (n : Nat) (h : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by -- @exo
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  clear h
  induction k with
  | zero => decide
  | succ k ih =>
    have h1 : 2 * (k + 4) + 1 ≤ (k + 4) ^ 2 := by grind
    rw [show k + 1 + 4 = (k + 4) + 1 by omega, Nat.pow_succ 2]
    have h2 : (k + 4 + 1) ^ 2 = (k + 4) ^ 2 + 2 * (k + 4) + 1 := by grind
    omega""",
 ["Écris `n = k + 4` (`obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩`) et fais une récurrence sur `k`.", "Pas de récurrence : `(k+5)² = (k+4)² + 2(k+4) + 1 ≤ 2·(k+4)² ≤ 2·2^(k+4)`. Établis `2(k+4) + 1 ≤ (k+4)²` avec `grind`, puis `omega`."], NSR, requiert="Recurrence.Croissance")
exo("Recurrence", "SommePuissancesPonderees", "Une somme pondérée", 3, [RD],
 """`Σ k·2ᵏ` pour `k` de 0 à `n` vaut `(n − 1)·2ⁿ⁺¹ + 2`. Pour éviter la soustraction, on écrit :
`Σ k·2ᵏ + 2ⁿ⁺¹ = n·2ⁿ⁺¹ + 2`.

## À prouver
`somme_ponderee (n : Nat) : somme (fun k => k * 2 ^ k) (n + 1) + 2 ^ (n + 1) = n * 2 ^ (n + 1) + 2`""",
 """theorem somme_ponderee (n : Nat) :
    somme (fun k => k * 2 ^ k) (n + 1) + 2 ^ (n + 1) = n * 2 ^ (n + 1) + 2 := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ, Nat.pow_succ 2 (n + 1)]
    grind""",
 ["Récurrence ; `somme_succ` et `Nat.pow_succ`, puis `grind` avec l'hypothèse de récurrence."], NSR, requiert="Recurrence.Geometrique")
exo("Recurrence", "TroisEtDeux", "Trois puissance n", 2, [RD],
 """`3ⁿ ≥ 2ⁿ + n` pour tout `n`.

## À prouver
`trois_puissance (n : Nat) : 2 ^ n + n ≤ 3 ^ n`""",
 """theorem trois_puissance (n : Nat) : 2 ^ n + n ≤ 3 ^ n := by -- @exo
  induction n with
  | zero => decide
  | succ n ih =>
    have h : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [Nat.pow_succ, Nat.pow_succ]
    omega""",
 ["Récurrence ; `Nat.pow_succ` sur les deux puissances.", "Il faut savoir que `2 ^ n ≥ 1` (`Nat.one_le_two_pow`), puis `omega`."], NSR, requiert="Recurrence.Croissance")

ecrire_tout()
