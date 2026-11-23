/- @parcours
titre: Le postulat de Bertrand, vérifié
difficulte: 1
requiert: Arithmetique.Goldbach100
indice: Un calcul : `decide +kernel` cherche le premier pour chaque `n`.
-/
import Solutions.Arithmetique.Goldbach100

/-!
# Le postulat de Bertrand, vérifié

Joseph Bertrand a conjecturé en 1845 qu'entre `n` et `2n` (strictement, pour `n ≥ 2`), il y a toujours un nombre premier.
Tchebychev l'a prouvé en 1852 ; on dit encore « postulat ». La preuve de Paul Erdős (1932, à
19 ans !) est un bijou… mais longue. Vérifions-le pour les petits `n`.

## À prouver
`bertrand_petits : ∀ n, 2 ≤ n → n < 60 → ∃ p, p < 2 * n ∧ n < p ∧ premierB p`

## Ressources
- [Postulat de Bertrand (Wikipédia)](https://fr.wikipedia.org/wiki/Postulat_de_Bertrand)
-/

namespace Parcours.Arith

theorem bertrand_petits : ∀ n, n < 60 → 2 ≤ n → ∃ p, p < 2 * n ∧ n < p ∧ premierB p = true := by -- @exo
  decide +kernel

end Parcours.Arith

#verifier
