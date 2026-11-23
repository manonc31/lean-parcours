/- @parcours
titre: La racine carrée entière
difficulte: 3
requiert: Programmes.DivisionSoustraction
indice: Pour `racineAux_le` : récurrence sur `k`, `simp only [racineAux]`, `split` ; dans les deux cas, c'est une hypothèse.
indice: Pour `racineAux_lt` : dans le cas « else », la condition est fausse : `Nat.not_le.mp` donne `n < (k + 1) * (k + 1)`.
indice: Pour `racine_spec`, il reste à voir `n < (n + 1) * (n + 1)` : `Nat.le_mul_of_pos_right`.
-/
import Solutions.Programmes.Definitions

/-!
# La racine carrée entière

`racine n` est le plus grand entier `r` tel que `r² ≤ n`. Le programme essaie `n, n − 1, …`
jusqu'à trouver un `r` qui convient (lent, mais facile à prouver !).

## À prouver
1. `racineAux_le : (racineAux n k)² ≤ n`
2. `racineAux_lt : n < (k + 1)² → n < (racineAux n k + 1)²`
3. `racine_spec : r * r ≤ n ∧ n < (r + 1) * (r + 1)` où `r = racine n`
4. `racine_mille : racine 1000 = 31`
-/

namespace Parcours.Prog

def racineAux (n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => if (k + 1) * (k + 1) ≤ n then k + 1 else racineAux n k

def racine (n : Nat) : Nat := racineAux n n

theorem racineAux_le (n k : Nat) : racineAux n k * racineAux n k ≤ n := by -- @exo
  induction k with
  | zero => simp [racineAux]
  | succ k ih =>
    simp only [racineAux]
    split <;> assumption

theorem racineAux_lt (n k : Nat) (h : n < (k + 1) * (k + 1)) :
    n < (racineAux n k + 1) * (racineAux n k + 1) := by -- @exo
  induction k with
  | zero => simpa [racineAux] using h
  | succ k ih =>
    simp only [racineAux]
    split
    · exact h
    · rename_i h'
      exact ih (Nat.not_le.mp h')

theorem racine_spec (n : Nat) :
    racine n * racine n ≤ n ∧ n < (racine n + 1) * (racine n + 1) := by -- @exo
  refine ⟨racineAux_le n n, racineAux_lt n n ?_⟩
  have : n + 1 ≤ (n + 1) * (n + 1) := Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem racine_mille : racine 1000 = 31 := by -- @exo
  decide +kernel

end Parcours.Prog

#verifier
