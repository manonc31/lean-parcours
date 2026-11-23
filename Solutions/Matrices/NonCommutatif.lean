/- @parcours
titre: Le produit n'est pas commutatif
difficulte: 1
requiert: Matrices.Associativite
indice: Essaie `A = ⎛0 1⎞` et `B = ⎛0 0⎞` (en Lean : `⟨0, 1, 0, 0⟩` et `⟨0, 0, 1, 0⟩`).
indice: Une fois les matrices données, `decide` vérifie `A * B ≠ B * A`.
-/
import Solutions.Matrices.Definitions

/-!
# Le produit n'est pas commutatif

Contrairement aux nombres, `AB ≠ BA` en général ! Trouve deux matrices qui ne commutent pas.

## À prouver
`non_commutatif : ∃ A B : M2, A * B ≠ B * A`
-/

namespace Parcours.Matrices

theorem non_commutatif : ∃ A B : M2, A * B ≠ B * A := by -- @exo
  exact ⟨⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, by decide⟩

end Parcours.Matrices

#verifier
