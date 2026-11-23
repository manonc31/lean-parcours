/- @parcours
titre: Le problème de Josèphe
difficulte: 4
requiert: Terminaison.Logarithme
indice: Récurrence sur `m` en généralisant `l`. Pour `m = 0`, `l = 0` et `josephe 1 = 1`.
indice: Pour `m + 1` : écris `l = 2 * l'` ou `l = 2 * l' + 1` (`Nat.even_or_odd'` n'existe pas sans Mathlib : utilise `l % 2` et `omega` pour construire `l'`).
indice: Alors `n = 2 ^ (m+1) + l` vaut `2 * (2 ^ m + l')` (+ 1) : déplie `josephe` une fois (`rw [josephe]`), puis `ih l'` donne `josephe (2 ^ m + l') = 2 * l' + 1`. `Nat.pow_succ` et `omega` concluent.
-/
import Solutions.Recurrence.Definitions

/-!
# Le problème de Josèphe

`n` personnes en cercle, numérotées de 1 à `n`. On élimine **une personne sur deux** (la 2, la 4, …)
en tournant, jusqu'à ce qu'il n'en reste qu'une. Qui survit ? (L'historien Flavius Josèphe aurait
utilisé ce calcul pour survivre, en l'an 67.)

En analysant un tour de cercle, on trouve la récurrence :
`J(1) = 1`, `J(2k) = 2 J(k) − 1`, `J(2k + 1) = 2 J(k) + 1`.

Et une formule magique : si `n = 2ᵐ + l` avec `l < 2ᵐ`, alors `J(n) = 2l + 1`.
(En binaire : on fait tourner le premier chiffre de `n` à la fin !)

## À prouver
`josephe_formule (m l : Nat) (hl : l < 2 ^ m) : josephe (2 ^ m + l) = 2 * l + 1`

## Ressources
- [Problème de Josèphe (Wikipédia)](https://fr.wikipedia.org/wiki/Probl%C3%A8me_de_Jos%C3%A8phe)
-/

namespace Parcours.Enigmes

def josephe (n : Nat) : Nat :=
  if n ≤ 1 then 1
  else if n % 2 = 0 then 2 * josephe (n / 2) - 1
  else 2 * josephe (n / 2) + 1
termination_by n
decreasing_by all_goals omega

theorem josephe_formule (m l : Nat) (hl : l < 2 ^ m) : josephe (2 ^ m + l) = 2 * l + 1 := by -- @exo
  induction m generalizing l with
  | zero =>
    have : l = 0 := by simp at hl; omega
    subst this
    rw [josephe]
    simp
  | succ m ih =>
    have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
    have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    rw [josephe, ite_eq_right (by omega)]
    by_cases hpair : l % 2 = 0
    · obtain ⟨l', rfl⟩ : ∃ l', l = 2 * l' := ⟨l / 2, by omega⟩
      rw [ite_eq_left (by omega), show (2 ^ (m + 1) + 2 * l') / 2 = 2 ^ m + l' by omega, ih l' (by omega)]
      omega
    · obtain ⟨l', rfl⟩ : ∃ l', l = 2 * l' + 1 := ⟨l / 2, by omega⟩
      rw [ite_eq_right (by omega), show (2 ^ (m + 1) + (2 * l' + 1)) / 2 = 2 ^ m + l' by omega,
        ih l' (by omega)]

end Parcours.Enigmes

#verifier
