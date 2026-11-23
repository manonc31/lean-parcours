/- @parcours
titre: Zéro à gauche
difficulte: 2
indice: `a + 0 = a` est vrai par définition, mais pas `0 + a = a` : il faut une récurrence sur `n`.
indice: `induction n with` puis `| zero => …` et `| succ n ih => …`.
indice: Cas `zero` : le but est `0 + 0 = 0`, c'est exactement `add_zero 0` (ou `rfl`).
indice: Cas `succ` : `rw [add_succ, ih]`.
-/
import Solutions.Naturels.Base

/-!
# Zéro à gauche

Par définition, `a + 0 = a` (`add_zero`). Mais `0 + a = a` n'est **pas** vrai par définition :
l'addition « regarde » son second argument. Il faut une **récurrence**.

## À prouver
`zero_add (n : ℕ) : 0 + n = n`

## Rappel
- `add_zero a : a + 0 = a`
- `add_succ a b : a + succ b = succ (a + b)`
- `induction n with | zero => … | succ n ih => …`

## Ressources
- [Raisonnement par récurrence (Wikipédia)](https://fr.wikipedia.org/wiki/Raisonnement_par_r%C3%A9currence)
-/

namespace Parcours.ℕ

theorem zero_add (n : ℕ) : 0 + n = n := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih => rw [add_succ, ih]

end Parcours.ℕ

#verifier
