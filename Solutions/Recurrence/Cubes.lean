/- @parcours
titre: Le théorème de Nicomaque
difficulte: 4
indice: Étape 1 : prouve `4 * somme cubes (n + 1) = (n * (n + 1)) ^ 2` par récurrence (comme les carrés).
indice: Étape 2 : d'après Gauss, `2 * S = n * (n + 1)` où `S = somme (fun i => i) (n + 1)`. Donc `4 * Σcubes = (2 * S) ^ 2 = 4 * S ^ 2`.
indice: Pour simplifier par 4 : `Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4)`.
-/
import Solutions.Recurrence.Gauss

/-!
# Le théorème de Nicomaque

`1³ + 2³ + ⋯ + n³ = (1 + 2 + ⋯ + n)²`. Une coïncidence magnifique, connue depuis l'Antiquité
(Nicomaque de Gérase, vers l'an 100).

## À prouver
`nicomaque (n : Nat) : somme (fun i => i ^ 3) (n + 1) = (somme (fun i => i) (n + 1)) ^ 2`

## Ressources
- [Théorème de Nicomaque (Wikipédia)](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_de_Nicomaque)
-/

namespace Parcours.Recurrence

theorem nicomaque (n : Nat) :
    somme (fun i => i ^ 3) (n + 1) = (somme (fun i => i) (n + 1)) ^ 2 := by -- @exo
  have h4 : ∀ n, 4 * somme (fun i => i ^ 3) (n + 1) = (n * (n + 1)) ^ 2 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [somme_succ, Nat.mul_add, ih]
      grind
  have hg := gauss n
  apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4)
  rw [h4, ← hg]
  grind

end Parcours.Recurrence

#verifier
