import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fabrique import exo, ecrire_tout

AD = "Solutions.Arithmetique.Definitions"
NS = "Parcours.Olymp"

def ol(ident, titre, diff, imports, texte, code, indices, requiert, ressources=(), opens=""):
    exo("Olympiades", ident, titre, diff, imports, texte, (opens + code).strip(), indices, NS,
        requiert=requiert, ressources=ressources)

ol("IMO1964b", "IMO 1964, problème 1 (b)", 2, ["Solutions.Olympiades.IMO1964"],
"""> Montrer qu'il n'existe aucun entier `n` tel que `2ⁿ + 1` soit divisible par 7.

Les restes de `2ⁿ` modulo 7 sont `1, 2, 4` : en ajoutant 1, on obtient `2, 3, 5`, jamais 0.

## À prouver
`imo1964b : (2 ^ n + 1) % 7 ≠ 0`""",
"""theorem imo1964b (n : Nat) : (2 ^ n + 1) % 7 ≠ 0 := by -- @exo
  have h := reste_puissance_deux n
  repeat' split at h
  all_goals omega""",
["Réutilise `reste_puissance_deux` (la première partie), puis `repeat' split at h` et `omega`."], "Olympiades.IMO1964")

ol("CinqTrente", "n⁵ − n est divisible par 30", 2, [AD],
"""Pour tout entier `n`, `n⁵ − n` est divisible par 2, par 3 et par 5, donc par 30.
La méthode des restes : `n⁵ mod 30` ne dépend que de `n mod 30`, et il n'y a que 30 restes à
essayer.

## À prouver
1. `puissance_cinq_mod : n ^ 5 % 30 = n % 30`
2. `cinq_trente : (n ^ 5 - n) % 30 = 0`""",
"""theorem puissance_cinq_mod (n : Nat) : n ^ 5 % 30 = n % 30 := by -- @exo
  rw [Nat.pow_mod]
  have : n % 30 < 30 := Nat.mod_lt _ (by decide)
  generalize n % 30 = r at this ⊢
  revert r
  decide

theorem cinq_trente (n : Nat) : (n ^ 5 - n) % 30 = 0 := by -- @exo
  have h := puissance_cinq_mod n
  have h2 : n ≤ n ^ 5 := Nat.le_self_pow (by decide) n
  omega""",
["`Nat.pow_mod : a ^ b % n = (a % n) ^ b % n`.", "Puis `generalize n % 30 = r`, `revert r` et `decide` essaie les 30 restes.", "Pour la soustraction : `Nat.le_self_pow`."], "Olympiades.Cinquieme")

ol("CinqConsecutifs", "Cinq entiers consécutifs", 3, ["Solutions.Arithmetique.Congruences"],
"""Le produit de 5 entiers consécutifs est toujours divisible par `5! = 120`. (En général, le produit
de `k` entiers consécutifs est divisible par `k!`, car le quotient est un coefficient binomial.)

Ici, on utilise **tes** lemmes de congruences : chaque facteur est congru à son reste modulo 120,
donc le produit aussi ; et il ne reste que 120 cas à vérifier.

## À prouver
`cinq_consecutifs : (n * (n + 1) * (n + 2) * (n + 3) * (n + 4)) % 120 = 0`""",
"""theorem cinq_consecutifs (n : Nat) : (n * (n + 1) * (n + 2) * (n + 3) * (n + 4)) % 120 = 0 := by -- @exo
  have h : n ≡ n % 120 [mod 120] := by
    unfold Congru
    exact (Nat.mod_mod _ _).symm
  have h' := congru_mul (congru_mul (congru_mul (congru_mul h (congru_add h (congru_refl 120 1)))
    (congru_add h (congru_refl 120 2))) (congru_add h (congru_refl 120 3)))
    (congru_add h (congru_refl 120 4))
  unfold Congru at h'
  rw [h']
  have : n % 120 < 120 := Nat.mod_lt _ (by decide)
  generalize n % 120 = r at this ⊢
  revert r
  decide""",
["`n ≡ n % 120 [mod 120]` (c'est `Nat.mod_mod`).", "Combine avec `congru_add` et `congru_mul` pour obtenir la même congruence pour le produit.", "Il reste 120 cas : `generalize n % 120 = r`, `revert r`, `decide`."], "Olympiades.CinqTrente", opens="open Parcours.Arith\n\n")

ol("TroisCarres", "Trois divise une somme de deux carrés", 2, [AD],
"""Si `3` divise `a² + b²`, alors `3` divise `a` et `b`. Les carrés modulo 3 valent 0 ou 1 :
pour que la somme fasse 0, il faut deux 0.

## À prouver
`trois_divise_carres : (a * a + b * b) % 3 = 0 → a % 3 = 0 ∧ b % 3 = 0`""",
"""theorem trois_divise_carres (a b : Nat) (h : (a * a + b * b) % 3 = 0) : a % 3 = 0 ∧ b % 3 = 0 := by -- @exo
  have ha : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  have hb : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
    simp [Nat.add_mod, Nat.mul_mod, ha, hb] at h ⊢""",
["Neuf cas selon les restes de `a` et `b` modulo 3, puis `simp [Nat.add_mod, Nat.mul_mod, ha, hb] at h ⊢`."], "Olympiades.Parite")

ol("Descente", "La descente infinie", 4, ["Solutions.Olympiades.TroisCarres"],
"""L'équation `x² + y² = 3z²` n'a que la solution `x = y = z = 0`.

## Se le représenter
C'est la **descente infinie** de Fermat : si `(x, y, z)` est une solution, alors 3 divise `x` et `y`
(exercice précédent), donc `9` divise `3z²`, donc 3 divise `z`, et `(x/3, y/3, z/3)` est une solution
**plus petite**. On ne peut pas descendre indéfiniment dans les entiers naturels : il faut que tout
soit nul.

En Lean, la descente infinie est une **récurrence forte** sur `z`.

## À prouver
`descente : x * x + y * y = 3 * (z * z) → x = 0 ∧ y = 0 ∧ z = 0`""",
"""theorem descente : ∀ z x y : Nat, x * x + y * y = 3 * (z * z) → x = 0 ∧ y = 0 ∧ z = 0 := by -- @exo
  intro z
  induction z using Nat.strongRecOn with
  | ind z ih =>
    intro x y h
    obtain ⟨hx, hy⟩ := trois_divise_carres x y (by omega)
    obtain ⟨a, rfl⟩ : ∃ a, x = 3 * a := ⟨x / 3, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, y = 3 * b := ⟨y / 3, by omega⟩
    have e1 : 3 * a * (3 * a) + 3 * b * (3 * b) = 9 * (a * a + b * b) := by grind
    have hz : z % 3 = 0 := by
      have : (z * z) % 3 = 0 := by omega
      have hz3 : z % 3 = 0 ∨ z % 3 = 1 ∨ z % 3 = 2 := by omega
      rcases hz3 with h3 | h3 | h3 <;> simp [Nat.mul_mod, h3] at this ⊢
    obtain ⟨c, rfl⟩ : ∃ c, z = 3 * c := ⟨z / 3, by omega⟩
    have e2 : 3 * c * (3 * c) = 9 * (c * c) := by grind
    have h' : a * a + b * b = 3 * (c * c) := by omega
    by_cases hc : c = 0
    · subst hc
      have ha : a * a = 0 := by omega
      have hb : b * b = 0 := by omega
      have ha' : a = 0 := (Nat.mul_eq_zero.mp ha).elim id id
      have hb' : b = 0 := (Nat.mul_eq_zero.mp hb).elim id id
      subst ha' hb'
      simp
    · have := ih c (by omega) a b h'
      omega""",
["Récurrence forte sur `z` : `induction z using Nat.strongRecOn`.", "Avec `trois_divise_carres`, écris `x = 3a`, `y = 3b` (`obtain ⟨a, rfl⟩ : ∃ a, x = 3 * a := ⟨x / 3, by omega⟩`). Puis montre que `3` divise `z`, et écris `z = 3c`.", "On obtient `a² + b² = 3c²` avec `c < z` (si `c ≠ 0`) : l'hypothèse de récurrence dit `c = 0`, contradiction. Et si `c = 0`, tout est nul."], "Olympiades.TroisCarres",
ressources=["[Descente infinie (Wikipédia)](https://fr.wikipedia.org/wiki/Descente_infinie)"])

ol("Repunits", "11, 111, 1111… ne sont jamais des carrés", 3, [AD],
"""Les **répunits** sont les nombres qui ne s'écrivent qu'avec des 1. Aucun (à part 1) n'est un carré !

## Se le représenter
Un carré vaut 0 ou 1 modulo 4 (pair : `(2k)² = 4k²` ; impair : `(2k+1)² = 4k² + 4k + 1`). Or
`11…11 = 11…00 + 11` et `100` est multiple de 4 : un répunit d'au moins deux chiffres vaut
`11 ≡ 3 (mod 4)`.

## À prouver
1. `carre_mod_quatre : k * k % 4 = 0 ∨ k * k % 4 = 1`
2. `repunit_mod_quatre : repunit (n + 2) % 4 = 3`
3. `repunit_pas_carre : k * k ≠ repunit (n + 2)`""",
"""def repunit : Nat → Nat
  | 0 => 0
  | n + 1 => 10 * repunit n + 1

theorem carre_mod_quatre (k : Nat) : k * k % 4 = 0 ∨ k * k % 4 = 1 := by -- @exo
  have : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases this with h | h | h | h <;> simp [Nat.mul_mod, h]

theorem repunit_mod_quatre (n : Nat) : repunit (n + 2) % 4 = 3 := by -- @exo
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 from rfl, repunit]
    omega

theorem repunit_pas_carre (n k : Nat) : k * k ≠ repunit (n + 2) := by -- @exo
  intro h
  have h1 := carre_mod_quatre k
  have h2 := repunit_mod_quatre n
  omega""",
["`carre_mod_quatre` : quatre cas selon `k % 4`, puis `simp [Nat.mul_mod, h]`.", "`repunit_mod_quatre` : récurrence ; `repunit (m + 1) = 10 * repunit m + 1`, et `omega`."], "Olympiades.Parite")

ol("DernierChiffre", "Le dernier chiffre de 7²⁰²⁵", 2, [AD],
"""Quel est le dernier chiffre de `7²⁰²⁵` (un nombre de 1712 chiffres) ? Les derniers chiffres des
puissances de 7 forment un cycle : `7, 9, 3, 1, 7, 9, 3, 1…` (car `7⁴ = 2401` finit par 1).
Comme `2025 = 4 × 506 + 1`, c'est **7**.

## À prouver
1. `sept_cycle : 7 ^ (4 * k + 1) % 10 = 7`
2. `dernier_chiffre : 7 ^ 2025 % 10 = 7` (sans calculer `7²⁰²⁵` !)""",
"""theorem sept_cycle (k : Nat) : 7 ^ (4 * k + 1) % 10 = 7 := by -- @exo
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show 4 * (k + 1) + 1 = (4 * k + 1) + 4 by omega, Nat.pow_add, Nat.mul_mod, ih]

theorem dernier_chiffre : 7 ^ 2025 % 10 = 7 := by -- @exo
  rw [show (2025 : Nat) = 4 * 506 + 1 from rfl]
  exact sept_cycle 506""",
["Récurrence sur `k` : `7^(4(k+1)+1) = 7^(4k+1) × 7⁴` (`Nat.pow_add`), puis `Nat.mul_mod`.", "Pour 2025 : réécris d'abord `2025` en `4 * 506 + 1` (`show (2025 : Nat) = 4 * 506 + 1 from rfl`), sinon Lean essaie de calculer `7²⁰²⁵`."], "Olympiades.Sept")

ol("TroisCubes", "Trois cubes consécutifs", 2, ["Solutions.Classiques.Divisible3"],
"""La somme de trois cubes consécutifs est toujours divisible par 9 : `1 + 8 + 27 = 36`,
`8 + 27 + 64 = 99`, `27 + 64 + 125 = 216`…

## Se le représenter
En développant : `n³ + (n+1)³ + (n+2)³ = 3(n³ + 2n) + 9(n² + n + 1)`. Et tu sais déjà que
`n³ + 2n` est divisible par 3 !

## À prouver
`trois_cubes : (n ^ 3 + (n + 1) ^ 3 + (n + 2) ^ 3) % 9 = 0`""",
"""theorem trois_cubes (n : Nat) : (n ^ 3 + (n + 1) ^ 3 + (n + 2) ^ 3) % 9 = 0 := by -- @exo
  have h := Parcours.Classiques.divisible_trois n
  obtain ⟨k, hk⟩ : ∃ k, n * n * n + 2 * n = 3 * k := ⟨(n * n * n + 2 * n) / 3, by omega⟩
  have e : n ^ 3 + (n + 1) ^ 3 + (n + 2) ^ 3 = 9 * (k + n + n * n + 1) := by grind
  rw [e]
  omega""",
["Réutilise `Parcours.Classiques.divisible_trois`, et écris `n³ + 2n = 3k`.", "Puis montre `n³ + (n+1)³ + (n+2)³ = 9(k + n + n² + 1)` avec `grind`."], "Classiques.Divisible3")

ol("CubesMod9", "Les sommes de trois cubes", 2, [AD],
"""Quels nombres sont sommes de trois cubes ? Un cube vaut toujours 0, 1 ou 8 modulo 9. Donc une
somme de trois cubes ne vaut jamais 4 ou 5 modulo 9 ! Par exemple, 4, 13, 22, 31… ne sont pas
sommes de trois cubes.

(Pour les autres, c'est un problème célèbre : avec des entiers négatifs autorisés, on n'a trouvé
une décomposition de 42 qu'en 2019, avec des nombres de 17 chiffres et un calcul géant !)

## À prouver
1. `cube_mod_neuf : n ^ 3 % 9 = 0 ∨ n ^ 3 % 9 = 1 ∨ n ^ 3 % 9 = 8`
2. `pas_quatre : (x ^ 3 + y ^ 3 + z ^ 3) % 9 ≠ 4`""",
"""theorem cube_mod_neuf (n : Nat) : n ^ 3 % 9 = 0 ∨ n ^ 3 % 9 = 1 ∨ n ^ 3 % 9 = 8 := by -- @exo
  rw [Nat.pow_mod]
  have : n % 9 < 9 := Nat.mod_lt _ (by decide)
  generalize n % 9 = r at this ⊢
  revert r
  decide

theorem pas_quatre (x y z : Nat) : (x ^ 3 + y ^ 3 + z ^ 3) % 9 ≠ 4 := by -- @exo
  have hx := cube_mod_neuf x
  have hy := cube_mod_neuf y
  have hz := cube_mod_neuf z
  omega""",
["`Nat.pow_mod`, puis les 9 restes possibles avec `decide`.", "Pour la somme : `omega` combine les trois possibilités pour chaque cube."], "Olympiades.CinqTrente",
ressources=["[Somme de trois cubes (Wikipédia)](https://fr.wikipedia.org/wiki/Somme_de_trois_cubes)"])

ol("Jamais121", "n² + 3n + 5 et 121", 3, [AD],
"""Un classique des olympiades : `n² + 3n + 5` n'est **jamais** divisible par 121.

## Se le représenter
`4(n² + 3n + 5) = (2n + 3)² + 11`. Si 121 divisait le membre de gauche, 11 diviserait `(2n+3)²`,
donc `2n + 3`, donc 121 diviserait `(2n+3)²`… et donc 11 : absurde.

En Lean, on peut aussi écrire `n = 121q + r` et vérifier les 121 restes.

## À prouver
`jamais_121 : (n * n + 3 * n + 5) % 121 ≠ 0`""",
"""theorem jamais_121 (n : Nat) : (n * n + 3 * n + 5) % 121 ≠ 0 := by -- @exo
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 121 ∧ n = 121 * q + r :=
    ⟨n / 121, n % 121, Nat.mod_lt _ (by decide), (Nat.div_add_mod n 121).symm⟩
  have e : (121 * q + r) * (121 * q + r) + 3 * (121 * q + r) + 5 =
      121 * (121 * q * q + 2 * q * r + 3 * q) + (r * r + 3 * r + 5) := by grind
  rw [e, Nat.mul_add_mod]
  clear e
  revert r
  decide""",
["Écris `n = 121q + r` avec `r < 121` (`Nat.div_add_mod`).", "Développe avec `grind`, puis `Nat.mul_add_mod : (m * x + y) % m = y % m`.", "Il reste 121 cas : efface les hypothèses qui parlent de `q` (`clear`), puis `revert r` et `decide`."], "Olympiades.CinqTrente")

ol("PasUnCarre", "n² + n + 1 n'est pas un carré", 2, [AD],
"""Pour `n ≥ 1`, `n² + n + 1` est coincé strictement entre deux carrés consécutifs :
`n² < n² + n + 1 < (n + 1)² = n² + 2n + 1`. Donc ce n'est pas un carré.

## À prouver
`pas_un_carre : 1 ≤ n → k * k ≠ n * n + n + 1`""",
"""theorem pas_un_carre (n k : Nat) (hn : 1 ≤ n) : k * k ≠ n * n + n + 1 := by -- @exo
  intro h
  rcases Nat.lt_or_ge n k with hk | hk
  · have h1 : (n + 1) * (n + 1) ≤ k * k := Nat.mul_le_mul hk hk
    have e : (n + 1) * (n + 1) = n * n + 2 * n + 1 := by grind
    omega
  · have : k * k ≤ n * n := Nat.mul_le_mul hk hk
    omega""",
["Deux cas : `k ≤ n` ou `k ≥ n + 1` (`Nat.lt_or_ge`).", "`Nat.mul_le_mul : a ≤ b → c ≤ d → a * c ≤ b * d`. Puis `omega` (il traite `k * k` et `n * n` comme des inconnues)."], "Olympiades.EntreDeuxCarres")

ol("Pell", "L'équation de Pell-Fermat", 2, [AD],
"""Les solutions de `x² − 2y² = 1` : `(3, 2)`, `(17, 12)`, `(99, 70)`, `(577, 408)`… Il y en a une
infinité, et on passe de l'une à la suivante par `(x, y) ↦ (3x + 4y, 2x + 3y)`.
Ces fractions `x/y` approchent `√2` de plus en plus près : `577/408 ≈ 1,4142157`, l'approximation
d'une tablette babylonienne d'il y a 3800 ans !

## À prouver
1. `pell_suivant : x² − 2y² = 1 → (3x + 4y)² − 2(2x + 3y)² = 1`
2. `pell_solution : (pell n).1² − 2 (pell n).2² = 1` pour tout `n`
3. `pell_croissant : (pell n).2 < (pell (n + 1)).2` (donc une infinité de solutions)
4. `pell_cinq : pell 4 = (577, 408)`""",
"""def pell : Nat → Int × Int
  | 0 => (1, 0)
  | n + 1 => (3 * (pell n).1 + 4 * (pell n).2, 2 * (pell n).1 + 3 * (pell n).2)

theorem pell_suivant (x y : Int) (h : x ^ 2 - 2 * y ^ 2 = 1) :
    (3 * x + 4 * y) ^ 2 - 2 * (2 * x + 3 * y) ^ 2 = 1 := by -- @exo
  grind

theorem pell_solution (n : Nat) : (pell n).1 ^ 2 - 2 * (pell n).2 ^ 2 = 1 := by -- @exo
  induction n with
  | zero => decide
  | succ n ih => exact pell_suivant _ _ ih

theorem pell_positif (n : Nat) : 1 ≤ (pell n).1 ∧ 0 ≤ (pell n).2 := by -- @exo
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [pell]
    omega

theorem pell_croissant (n : Nat) : (pell n).2 < (pell (n + 1)).2 := by -- @exo
  have := pell_positif n
  simp only [pell]
  omega

theorem pell_cinq : pell 4 = (577, 408) := by -- @exo
  decide""",
["`pell_suivant` : `grind` développe tout.", "`pell_solution` : récurrence.", "Pour la croissance, prouve d'abord que `x ≥ 1` et `y ≥ 0` (`pell_positif`), puis `omega`."], "Olympiades.SommeCubes",
ressources=["[Équation de Pell-Fermat (Wikipédia)](https://fr.wikipedia.org/wiki/%C3%89quation_de_Pell-Fermat)"])

ol("CauchyNat", "L'équation de Cauchy", 2, [AD],
"""Une équation fonctionnelle : trouver toutes les fonctions `f : ℕ → ℕ` telles que
`f(x + y) = f(x) + f(y)` pour tous `x, y`. Réponse : les fonctions linéaires `f(n) = n × f(1)`.

## À prouver
`cauchy_nat : (∀ x y, f (x + y) = f x + f y) → ∀ n, f n = n * f 1`""",
"""theorem cauchy_nat (f : Nat → Nat) (h : ∀ x y, f (x + y) = f x + f y) : ∀ n, f n = n * f 1 := by -- @exo
  intro n
  induction n with
  | zero =>
    have := h 0 0
    simp at this
    simp
    omega
  | succ n ih => rw [h n 1, ih, Nat.succ_mul]""",
["Commence par `f 0` : `h 0 0` dit `f 0 = f 0 + f 0`.", "Puis récurrence : `f (n + 1) = f n + f 1`."], "Olympiades.IMO1977")

ol("PointFixe", "Une équation fonctionnelle", 1, [AD],
"""Soit `f : ℕ → ℕ` telle que `f(n) ≥ n` et `f(f(n)) ≤ n` pour tout `n`. Alors `f` est l'identité !

## Se le représenter
`n ≤ f(n) ≤ f(f(n)) ≤ n` : tout est égal. (La deuxième inégalité vient de la première propriété
appliquée à `f(n)`.)

## À prouver
`point_fixe : (∀ n, n ≤ f n) → (∀ n, f (f n) ≤ n) → ∀ n, f n = n`""",
"""theorem point_fixe (f : Nat → Nat) (h1 : ∀ n, n ≤ f n) (h2 : ∀ n, f (f n) ≤ n) : ∀ n, f n = n := by -- @exo
  intro n
  have a := h1 n
  have b := h1 (f n)
  have c := h2 n
  omega""",
["Applique `h1` à `n` et à `f n`, et `h2` à `n` ; puis `omega`."], "Olympiades.Parite")

ol("HuitABC", "(a + b)(b + c)(c + a) ≥ 8abc", 3, ["Solutions.Classiques.CauchySchwarz"],
"""Pour `a, b, c ≥ 0` : `(a + b)(b + c)(c + a) ≥ 8abc`. On peut le voir avec AM-GM
(`a + b ≥ 2√ab`…), mais il y a plus simple : la différence vaut
`a(b − c)² + b(c − a)² + c(a − b)²`, une somme de termes positifs.

## À prouver
`huit_abc : 0 ≤ a → 0 ≤ b → 0 ≤ c → 8 * a * b * c ≤ (a + b) * (b + c) * (c + a)`""",
"""theorem huit_abc (a b c : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    8 * a * b * c ≤ (a + b) * (b + c) * (c + a) := by -- @exo
  have h1 := Int.mul_nonneg ha (Parcours.Classiques.carre_positif (b - c))
  have h2 := Int.mul_nonneg hb (Parcours.Classiques.carre_positif (c - a))
  have h3 := Int.mul_nonneg hc (Parcours.Classiques.carre_positif (a - b))
  grind""",
["Trois termes positifs : `Int.mul_nonneg ha (carre_positif (b - c))`, etc.", "Avec ces trois faits, `grind` conclut."], "Classiques.CauchySchwarz")

# --- Classiques : inégalités
NC = "Parcours.Classiques"
CS = "Solutions.Classiques.CauchySchwarz"
def cl(ident, titre, diff, imports, image, enonce, code, indices, requiert, ressources=()):
    texte = "## Se le représenter\n" + image.strip() + "\n\n## À prouver\n" + enonce.strip()
    exo("Classiques", ident, titre, diff, imports, texte, code.strip(), indices, NC, requiert=requiert, ressources=ressources)

cl("Reordonnement", "L'inégalité du réordonnement", 1, [CS],
"""Tu dois acheter `a` objets à un prix et `b` à un autre, avec `a ≤ b`, et tu peux choisir les prix
parmi `c ≤ d`. Pour payer le plus, on met le plus gros prix sur la plus grosse quantité :
`a·c + b·d ≥ a·d + b·c`. Visuellement : la différence est l'aire du rectangle `(b − a) × (d − c)`.""",
"`reordonnement : a ≤ b → c ≤ d → a * d + b * c ≤ a * c + b * d`",
"""theorem reordonnement (a b c d : Int) (h1 : a ≤ b) (h2 : c ≤ d) :
    a * d + b * c ≤ a * c + b * d := by -- @exo
  have h := Int.mul_nonneg (Int.sub_nonneg.mpr h1) (Int.sub_nonneg.mpr h2)
  grind""",
["`(b − a)(d − c) ≥ 0` : `Int.mul_nonneg` et `Int.sub_nonneg`.", "Puis `grind`."], "Classiques.CauchySchwarz",
ressources=["[Inégalité de réarrangement (Wikipédia)](https://fr.wikipedia.org/wiki/In%C3%A9galit%C3%A9_de_r%C3%A9arrangement)"])

cl("SommeCarresProduits", "x² + y² + z² ≥ xy + yz + zx", 2, [CS],
"""Additionne les trois carrés `(x − y)²`, `(y − z)²`, `(z − x)²` : c'est positif, et ça vaut
`2(x² + y² + z²) − 2(xy + yz + zx)`.""",
"`somme_carres_produits : x * y + y * z + z * x ≤ x ^ 2 + y ^ 2 + z ^ 2`",
"""theorem somme_carres_produits (x y z : Int) : x * y + y * z + z * x ≤ x ^ 2 + y ^ 2 + z ^ 2 := by -- @exo
  have h1 := carre_positif (x - y)
  have h2 := carre_positif (y - z)
  have h3 := carre_positif (z - x)
  grind""",
["Trois carrés positifs (`carre_positif`), puis `grind`."], "Classiques.CauchySchwarz")

cl("CubesProduits", "a³ + b³ ≥ a²b + ab²", 2, [CS],
"""Pour `a, b ≥ 0` : `a³ + b³ − a²b − ab² = (a + b)(a − b)²`, produit de deux nombres positifs.""",
"`cubes_produits : 0 ≤ a → 0 ≤ b → a ^ 2 * b + a * b ^ 2 ≤ a ^ 3 + b ^ 3`",
"""theorem cubes_produits (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 2 * b + a * b ^ 2 ≤ a ^ 3 + b ^ 3 := by -- @exo
  have h := Int.mul_nonneg (Int.add_nonneg ha hb) (carre_positif (a - b))
  grind""",
["`(a + b)(a − b)² ≥ 0` : `Int.mul_nonneg (Int.add_nonneg ha hb) (carre_positif (a - b))`."], "Classiques.SommeCarresProduits")

ecrire_tout()
