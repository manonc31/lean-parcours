/- @parcours
titre: L'inverse d'une matrice
difficulte: 3
requiert: Matrices.Determinant
indice: Comme d'habitude : coefficients, `simp only [adj, M2.det, M2.mul_def, M2.mk.injEq]`, `refine ⟨?_, ?_, ?_, ?_⟩ <;> grind`.
indice: Pour `inverse`, n'oublie pas de déplier `det` dans l'hypothèse `h` (`simp only [M2.det] at h`).
-/
import Solutions.Matrices.Definitions

/-!
# L'inverse d'une matrice

La matrice « adjointe » de `⎛a b⎞ / ⎝c d⎠` est `⎛d −b⎞ / ⎝−c a⎠`. Leur produit vaut `det × id`.
Donc une matrice de déterminant 1 est inversible, d'inverse son adjointe.

## À prouver
1. `mul_adj : A * adj A = ⟨det A, 0, 0, det A⟩`
2. `inverse : det A = 1 → A * adj A = id2 ∧ adj A * A = id2`
-/

namespace Parcours.Matrices

def adj (A : M2) : M2 := ⟨A.d, -A.b, -A.c, A.a⟩

theorem mul_adj (A : M2) : A * adj A = ⟨M2.det A, 0, 0, M2.det A⟩ := by -- @exo
  obtain ⟨a, b, c, d⟩ := A
  simp only [adj, M2.det, M2.mul_def, M2.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

theorem inverse (A : M2) (h : M2.det A = 1) : A * adj A = M2.id2 ∧ adj A * A = M2.id2 := by -- @exo
  obtain ⟨a, b, c, d⟩ := A
  simp only [M2.det] at h
  simp only [adj, M2.mul_def, M2.id2, M2.mk.injEq]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;> grind

end Parcours.Matrices

#verifier
