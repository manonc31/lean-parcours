/- @parcours
titre: Le nombre de chiffres
difficulte: 2
requiert: Programmes.Definitions
indice: `fun_induction nbChiffres n` : deux cas, `n < 10` et le cas récursif.
indice: `Nat.pow_succ : a ^ (n + 1) = a ^ n * a`, puis `omega` (il traite `10 ^ c` comme une inconnue).
indice: Pour `puissance_le`, écris `nbChiffres (n / 10) = c + 1` (grâce à `nbChiffres_pos`).
-/
import Solutions.Programmes.Definitions

/-!
# Le nombre de chiffres

Combien de chiffres a un nombre en base 10 ? On divise par 10 jusqu'à tomber sous 10.
La spécification : un nombre à `c` chiffres est entre `10^(c−1)` et `10^c`.

## À prouver
1. `nbChiffres_pos : 1 ≤ nbChiffres n`
2. `lt_puissance : n < 10 ^ nbChiffres n`
3. `puissance_le : 0 < n → 10 ^ (nbChiffres n - 1) ≤ n`
-/

namespace Parcours.Prog

def nbChiffres (n : Nat) : Nat := if n < 10 then 1 else nbChiffres (n / 10) + 1
termination_by n
decreasing_by omega

theorem nbChiffres_pos (n : Nat) : 1 ≤ nbChiffres n := by -- @exo
  fun_induction nbChiffres n <;> omega

theorem lt_puissance (n : Nat) : n < 10 ^ nbChiffres n := by -- @exo
  fun_induction nbChiffres n with
  | case1 n h => simpa using h
  | case2 n h ih =>
    rw [Nat.pow_succ]
    omega

theorem puissance_le (n : Nat) (h : 0 < n) : 10 ^ (nbChiffres n - 1) ≤ n := by -- @exo
  fun_induction nbChiffres n with
  | case1 n _ =>
    simp only [Nat.sub_self, Nat.pow_zero]
    omega
  | case2 n h' ih =>
    have ih := ih (by omega)
    obtain ⟨c, hc⟩ : ∃ c, nbChiffres (n / 10) = c + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos (nbChiffres_pos (n / 10))).symm⟩
    rw [hc] at ih ⊢
    simp only [Nat.add_sub_cancel] at ih ⊢
    rw [Nat.pow_succ]
    omega

end Parcours.Prog

#verifier
