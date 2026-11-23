/- @parcours
titre: Simplifier une somme
difficulte: 2
indice: Pour `add_right_cancel`, récurrence sur `c`. Attention, l'hypothèse `h` dépend de `c` : commence par `induction c with` AVANT d'introduire `h` (l'énoncé est écrit avec `→` exprès).
indice: Cas `succ` : `intro h`, `rw [add_succ, add_succ] at h`, puis `succ_inj h` donne `a + c = b + c`, et `ih` conclut.
indice: `add_left_cancel` découle de `add_right_cancel` et `add_comm`.
-/
import Solutions.Naturels.AddComm

/-!
# Simplifier une somme

Si `a + c = b + c`, alors `a = b`. Évident ? Il faut pourtant le prouver !
On utilisera l'injectivité du successeur : `succ_inj : succ a = succ b → a = b`.

## À prouver
1. `add_right_cancel (a b c : ℕ) : a + c = b + c → a = b`
2. `add_left_cancel (a b c : ℕ) : a + b = a + c → b = c`
-/

namespace Parcours.ℕ

theorem add_right_cancel (a b c : ℕ) : a + c = b + c → a = b := by -- @exo
  induction c with
  | zero =>
    intro h
    exact h
  | succ c ih =>
    intro h
    rw [add_succ, add_succ] at h
    exact ih (succ_inj h)

theorem add_left_cancel (a b c : ℕ) : a + b = a + c → b = c := by -- @exo
  intro h
  rw [add_comm a b, add_comm a c] at h
  exact add_right_cancel b c a h

end Parcours.ℕ

#verifier
