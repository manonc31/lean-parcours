/- @parcours
titre: L'identité remarquable (boss de ℕ)
difficulte: 4
debloque: anneau
indice: Commence par un lemme : `have pow_two : ∀ x : ℕ, x ^ (2 : ℕ) = x * x`. Preuve : `intro x; rw [two_eq_succ_one, pow_succ, pow_one]`.
indice: `rw [pow_two, pow_two, pow_two]`, puis développe avec `add_mul`, `mul_add`.
indice: Il reste à réorganiser : attention, `2 * a * b` se lit `(2 * a) * b`. `mul_assoc` le transforme en `2 * (a * b)`, puis `two_mul` en `a * b + a * b`. Et `mul_comm b a` pour le terme `b * a`.
indice: À la fin, une somme de 4 termes à réordonner : `add_assoc` et `add_comm` bien ciblés.
-/
import Solutions.Naturels.PowMul

/-!
# L'identité remarquable

`(a + b)² = a² + 2ab + b²`. Au collège, c'est une ligne. Ici, c'est le boss final
de l'arithmétique de Peano : il faut tout ce que tu as prouvé jusqu'ici.

🔑 **Récompense** : cet exercice débloque le jeton **`anneau`**. Dans les exercices qui en
dépendent, tu pourras utiliser la tactique `grind`, qui sait faire ce genre de calcul
toute seule (et bien plus). Tu as prouvé que tu savais le faire à la main !

## À prouver
`carre_somme (a b : ℕ) : (a + b) ^ (2 : ℕ) = a ^ (2 : ℕ) + 2 * a * b + b ^ (2 : ℕ)`
-/

namespace Parcours.ℕ

theorem carre_somme (a b : ℕ) : (a + b) ^ (2 : ℕ) = a ^ (2 : ℕ) + 2 * a * b + b ^ (2 : ℕ) := by -- @exo
  have pow_two : ∀ x : ℕ, x ^ (2 : ℕ) = x * x := by
    intro x
    rw [two_eq_succ_one, pow_succ, pow_one]
  rw [pow_two, pow_two, pow_two, add_mul, mul_add, mul_add, mul_assoc, two_mul,
    mul_comm b a, ← add_assoc, add_assoc (a * a) (a * b) (a * b)]

end Parcours.ℕ

#verifier
