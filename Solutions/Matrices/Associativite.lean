/- @parcours
titre: Le produit est associatif
difficulte: 2
indice: `obtain ⟨a, b, c, d⟩ := A` (idem pour `B`, `C`) fait apparaître les coefficients.
indice: `simp only [M2.mul_def, M2.mk.injEq]` transforme l'égalité de matrices en 4 égalités d'entiers ; `refine ⟨?_, ?_, ?_, ?_⟩ <;> grind`.
-/
import Solutions.Matrices.Definitions

/-!
# Le produit est associatif

Le produit de matrices est **associatif** : `(AB)C = A(BC)`. (Mais pas commutatif, voir l'exercice suivant !)

## À prouver
1. `mul_assoc : A * B * C = A * (B * C)`
2. `id_mul : id2 * A = A` et `mul_id : A * id2 = A`
-/

namespace Parcours.Matrices

theorem mul_assoc (A B C : M2) : A * B * C = A * (B * C) := by -- @exo
  obtain ⟨a, b, c, d⟩ := A
  obtain ⟨e, f, g, h⟩ := B
  obtain ⟨i, j, k, l⟩ := C
  simp only [M2.mul_def, M2.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

theorem id_mul (A : M2) : M2.id2 * A = A := by -- @exo
  obtain ⟨a, b, c, d⟩ := A
  simp only [M2.mul_def, M2.id2, M2.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

theorem mul_id (A : M2) : A * M2.id2 = A := by -- @exo
  obtain ⟨a, b, c, d⟩ := A
  simp only [M2.mul_def, M2.id2, M2.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

end Parcours.Matrices

#verifier
