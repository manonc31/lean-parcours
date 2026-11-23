/- @parcours
titre: Puissances dans un groupe
difficulte: 2
indice: `puiss_add` : récurrence sur `n`. Cas `succ` : `a ^ (m + (n+1)) = a ^ (m + n) * a` par définition (`show`), puis `ih` et `Groupe.mul_assoc`.
indice: `puiss_inv` : récurrence ; tu auras besoin de `mul_inv_rev` et de faire commuter `a` avec ses puissances : prouve d'abord `a ^ n * a = a * a ^ n`.
-/
import Solutions.Algebre.Inverses

/-!
# Puissances dans un groupe

`a ^ 0 = 1`, `a ^ (n + 1) = a ^ n * a`.

## À prouver
1. `puiss_add : a ^ (m + n) = a ^ m * a ^ n`
2. `puiss_comm : a ^ n * a = a * a ^ n`
3. `puiss_inv : (a⁻¹) ^ n = (a ^ n)⁻¹`
-/

namespace Parcours.Algebre

variable {G : Type} [Groupe G]

def puiss (a : G) : Nat → G
  | 0 => 1
  | n + 1 => puiss a n * a

instance instPuiss : HPow G Nat G := ⟨puiss⟩

theorem puiss_zero (a : G) : a ^ 0 = 1 := rfl
theorem puiss_succ (a : G) (n : Nat) : a ^ (n + 1) = a ^ n * a := rfl

theorem puiss_add (a : G) (m n : Nat) : a ^ (m + n) = a ^ m * a ^ n := by -- @exo
  induction n with
  | zero => rw [Nat.add_zero, puiss_zero, mul_one]
  | succ n ih => rw [← Nat.add_assoc, puiss_succ, ih, puiss_succ, Groupe.mul_assoc]

theorem puiss_comm (a : G) (n : Nat) : a ^ n * a = a * a ^ n := by -- @exo
  induction n with
  | zero => rw [puiss_zero, Groupe.one_mul, mul_one]
  | succ n ih => rw [puiss_succ, ih, Groupe.mul_assoc, ih]

theorem puiss_inv (a : G) (n : Nat) : (a⁻¹) ^ n = (a ^ n)⁻¹ := by -- @exo
  induction n with
  | zero => rw [puiss_zero, puiss_zero, inv_one]
  | succ n ih => rw [puiss_succ, puiss_succ, ih, puiss_comm, mul_inv_rev]

end Parcours.Algebre

#verifier
