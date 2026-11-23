/- @parcours
titre: Un algorithme pour ≤
difficulte: 3
indice: Programme `ble` par cas sur les deux arguments : `| zero, _ => true`, `| succ _, zero => false`, `| succ a, succ b => ble a b`.
indice: Pour la preuve : `induction a generalizing b with`, puis `cases b with` dans le cas `succ`.
indice: Cas `succ a`, `zero` : `ble (succ a) 0 = false`, donc il faut montrer que `succ a ≤ 0` est faux (`not_lt_zero`, car `succ a ≤ 0` c'est `a < 0`).
indice: Cas `succ a`, `succ b` : `ble (succ a) (succ b) = ble a b` par définition (`show ble a b = true ↔ _`), puis `ih b`, `succ_le_succ`, `le_of_succ_le_succ`.
-/
import Solutions.Naturels.Strict

/-!
# Un algorithme pour ≤

Jusqu'ici, `a ≤ b` est une **proposition** (`∃ c, b = a + c`) : on ne peut pas « calculer »
si elle est vraie. Écris une **fonction** `ble : ℕ → ℕ → Bool` qui répond `true` ou `false`,
puis **prouve** qu'elle donne toujours la bonne réponse.

C'est ton premier exercice « algorithme + preuve » : tu dois écrire la définition (remplace
le `sorry` de `ble`), puis prouver sa correction. Tu peux tester ta fonction avec
`#eval ble 3 5`.

Une fois prouvé, on en déduit une instance `Decidable (a ≤ b)` : la tactique `decide`
saura désormais vérifier des inégalités !

## À faire
1. `def ble : ℕ → ℕ → Bool` (à programmer, par récurrence)
2. `ble_correct (a b : ℕ) : ble a b = true ↔ a ≤ b`
-/

namespace Parcours.ℕ

def ble : ℕ → ℕ → Bool -- @exo
  | zero, _ => true
  | succ _, zero => false
  | succ a, succ b => ble a b

theorem ble_correct (a b : ℕ) : ble a b = true ↔ a ≤ b := by -- @exo
  induction a generalizing b with
  | zero => exact ⟨fun _ => zero_le b, fun _ => rfl⟩
  | succ a ih =>
    cases b with
    | zero =>
      constructor
      · intro h
        cases h
      · intro h
        exact absurd h (not_lt_zero a)
    | succ b =>
      show ble a b = true ↔ _
      rw [ih b]
      exact ⟨succ_le_succ a b, le_of_succ_le_succ a b⟩

instance (a b : ℕ) : Decidable (a ≤ b) :=
  decidable_of_iff (ble a b = true) (ble_correct a b)

end Parcours.ℕ

#verifier
