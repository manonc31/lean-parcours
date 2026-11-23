/- @parcours
celebre: 69
titre: Le PGCD divise
difficulte: 3
indice: Lemme 1 : `a = a % b + b * (a / b)` (`Nat.mod_add_div a b`). Donc si `d ∣ b` et `d ∣ a % b`, alors `d ∣ a` (`divise_add`, `divise_mul_droite`).
indice: Lemme 2 (`divise_mod`) : dans l'autre sens, avec `divise_sub`.
indice: `pgcd_divise` : `fun_induction pgcd a b with`. Cas `case1 a` : `pgcd a 0 = a`. Cas `case2 a b hb ih` : `ih` parle de `pgcd b (a % b)`.
indice: Si le but contient encore `pgcd a 0` ou `pgcd a b`, réécris avec `pgcd_zero` ou `pgcd_rec a b hb`.
-/
import Solutions.Arithmetique.DiviseOrdre

/-!
# Le PGCD divise

Montre que l'algorithme d'Euclide calcule bien un diviseur commun… et même le **plus grand**,
au sens où tout diviseur commun le divise.

## À prouver
1. `divise_de_mod : d ∣ b → d ∣ a % b → d ∣ a`
2. `divise_mod : d ∣ a → d ∣ b → d ∣ a % b`
3. `pgcd_divise (a b : Nat) : pgcd a b ∣ a ∧ pgcd a b ∣ b`
4. `divise_pgcd : d ∣ a → d ∣ b → d ∣ pgcd a b`
-/

namespace Parcours.Arith

theorem divise_de_mod {d a b : Nat} (h1 : d ∣ b) (h2 : d ∣ a % b) : d ∣ a := by -- @exo
  have h := Nat.mod_add_div a b
  rw [← h]
  exact divise_add h2 (divise_mul_droite h1 _)

theorem divise_mod {d a b : Nat} (h1 : d ∣ a) (h2 : d ∣ b) : d ∣ a % b := by -- @exo
  have h := Nat.mod_add_div a b
  rw [← h, Nat.add_comm] at h1
  exact divise_sub h1 (divise_mul_droite h2 _)

theorem pgcd_divise (a b : Nat) : pgcd a b ∣ a ∧ pgcd a b ∣ b := by -- @exo
  fun_induction pgcd a b with
  | case1 a => exact ⟨divise_refl a, divise_zero a⟩
  | case2 a b hb ih => exact ⟨divise_de_mod ih.1 ih.2, ih.1⟩

theorem divise_pgcd {d a b : Nat} (h1 : d ∣ a) (h2 : d ∣ b) : d ∣ pgcd a b := by -- @exo
  fun_induction pgcd a b with
  | case1 a => exact h1
  | case2 a b hb ih => exact ih h2 (divise_mod h1 h2)

end Parcours.Arith

#verifier
