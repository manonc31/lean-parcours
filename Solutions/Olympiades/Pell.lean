/- @parcours
titre: L'équation de Pell-Fermat
difficulte: 2
requiert: Olympiades.SommeCubes
indice: `pell_suivant` : `grind` développe tout.
indice: `pell_solution` : récurrence.
indice: Pour la croissance, prouve d'abord que `x ≥ 1` et `y ≥ 0` (`pell_positif`), puis `omega`.
-/
import Solutions.Arithmetique.Definitions

/-!
# L'équation de Pell-Fermat

Les solutions de `x² − 2y² = 1` : `(3, 2)`, `(17, 12)`, `(99, 70)`, `(577, 408)`… Il y en a une
infinité, et on passe de l'une à la suivante par `(x, y) ↦ (3x + 4y, 2x + 3y)`.
Ces fractions `x/y` approchent `√2` de plus en plus près : `577/408 ≈ 1,4142157`, l'approximation
d'une tablette babylonienne d'il y a 3800 ans !

## À prouver
1. `pell_suivant : x² − 2y² = 1 → (3x + 4y)² − 2(2x + 3y)² = 1`
2. `pell_solution : (pell n).1² − 2 (pell n).2² = 1` pour tout `n`
3. `pell_croissant : (pell n).2 < (pell (n + 1)).2` (donc une infinité de solutions)
4. `pell_cinq : pell 4 = (577, 408)`

## Ressources
- [Équation de Pell-Fermat (Wikipédia)](https://fr.wikipedia.org/wiki/%C3%89quation_de_Pell-Fermat)
-/

namespace Parcours.Olymp

def pell : Nat → Int × Int
  | 0 => (1, 0)
  | n + 1 => (3 * (pell n).1 + 4 * (pell n).2, 2 * (pell n).1 + 3 * (pell n).2)

theorem pell_suivant (x y : Int) (h : x ^ 2 - 2 * y ^ 2 = 1) :
    (3 * x + 4 * y) ^ 2 - 2 * (2 * x + 3 * y) ^ 2 = 1 := by -- @exo
  grind

theorem pell_solution (n : Nat) : (pell n).1 ^ 2 - 2 * (pell n).2 ^ 2 = 1 := by -- @exo
  induction n with
  | zero => decide
  | succ n ih => exact pell_suivant _ _ ih

theorem pell_positif (n : Nat) : 1 ≤ (pell n).1 ∧ 0 ≤ (pell n).2 := by -- @exo
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [pell]
    omega

theorem pell_croissant (n : Nat) : (pell n).2 < (pell (n + 1)).2 := by -- @exo
  have := pell_positif n
  simp only [pell]
  omega

theorem pell_cinq : pell 4 = (577, 408) := by -- @exo
  decide

end Parcours.Olymp

#verifier
