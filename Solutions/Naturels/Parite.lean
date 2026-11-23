/- @parcours
titre: Pair ou impair
difficulte: 3
indice: `pair_add` : `obtain ⟨k, rfl⟩ := ha`, `obtain ⟨l, rfl⟩ := hb`, puis le témoin `k + l` et un réarrangement (`add_assoc`, `add_comm`, `add_left_comm`…).
indice: `pair_ou_impair` : récurrence sur `n`. Si `n` est pair, `succ n` est « impair » (le second cas) ; si `succ n` est pair, alors `succ (succ n)` aussi : témoin `k + 1`.
indice: Pour `succ (succ (k + k)) = (k + 1) + (k + 1)` : `rw [succ_eq_add_one, succ_eq_add_one]` puis des `add_assoc`/`add_comm`… ou prouve-le à part avec `add_succ` et `succ_add`.
-/
import Solutions.Naturels.AddRightComm
import Solutions.Naturels.Successeur

/-!
# Pair ou impair

On définit : `n` est **pair** s'il existe `k` avec `n = k + k`.

## À prouver
1. `pair_add : Pair a → Pair b → Pair (a + b)`
2. `pair_ou_impair (n : ℕ) : Pair n ∨ Pair (succ n)` (tout entier est pair, ou son successeur l'est)
-/

namespace Parcours.ℕ

def Pair (n : ℕ) : Prop := ∃ k, n = k + k

theorem pair_add {a b : ℕ} (ha : Pair a) (hb : Pair b) : Pair (a + b) := by -- @exo
  obtain ⟨k, rfl⟩ := ha
  obtain ⟨l, rfl⟩ := hb
  refine ⟨k + l, ?_⟩
  rw [add_assoc, add_assoc, add_left_comm k l l]

theorem pair_ou_impair (n : ℕ) : Pair n ∨ Pair (succ n) := by -- @exo
  induction n with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ n ih =>
    rcases ih with ⟨k, hk⟩ | ⟨k, hk⟩
    · right
      refine ⟨succ k, ?_⟩
      rw [hk, add_succ, succ_add]
    · left
      exact ⟨k, hk⟩

end Parcours.ℕ

#verifier
