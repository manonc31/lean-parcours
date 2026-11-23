/- @parcours
titre: Le dernier chiffre des Fibonacci
difficulte: 3
requiert: Programmes.Kaprekar
indice: `repeter_add` : récurrence sur `n` en généralisant `x`.
indice: `etat_fib` : récurrence ; `fib (n + 2) = fib n + fib (n + 1)` et `Nat.add_mod`.
indice: Pour conclure : `repeter pasFib (n + 60) = repeter pasFib n ∘ repeter pasFib 60`.
-/
import Solutions.Programmes.Definitions

/-!
# Le dernier chiffre des Fibonacci

Les derniers chiffres des nombres de Fibonacci : `0, 1, 1, 2, 3, 5, 8, 3, 1, 4, 5, 9, 4, …` Ils se
répètent avec une période de **60** (la période de Pisano pour 10). Pourquoi périodique ? Le
dernier chiffre de `F(n+2)` ne dépend que de ceux de `F(n)` et `F(n+1)` : on se promène dans les
100 couples possibles, et on finit forcément par repasser par un couple déjà vu.

## À prouver
1. `pisano : repeter pasFib 60 (0, 1) = (0, 1)` et `pas_avant_60` : pas avant 60.
2. `repeter_add`, `repeter_succ'` : propriétés de `repeter`.
3. `etat_fib : repeter pasFib n (0, 1) = (fib n % 10, fib (n + 1) % 10)`
4. `dernier_chiffre_fib : fib (n + 60) % 10 = fib n % 10`

## Ressources
- [Période de Pisano (Wikipédia)](https://fr.wikipedia.org/wiki/P%C3%A9riode_de_Pisano)
-/

namespace Parcours.Prog

open Parcours.Recurrence

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
  exact (congrArg Prod.fst h).symm

end Parcours.Prog

#verifier
