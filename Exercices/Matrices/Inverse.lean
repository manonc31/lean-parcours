import Exercices.Matrices.Definitions

/-!
# L'inverse d'une matrice

La matrice « adjointe » de `⎛a b⎞ / ⎝c d⎠` est `⎛d −b⎞ / ⎝−c a⎠`. Leur produit vaut `det × id`.
Donc une matrice de déterminant 1 est inversible, d'inverse son adjointe.

## À prouver
1. `mul_adj : A * adj A = ⟨det A, 0, 0, det A⟩`
2. `inverse : det A = 1 → A * adj A = id2 ∧ adj A * A = id2`

---
*Exercice* `Matrices.Inverse` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Matrices.Inverse` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Matrices

def adj (A : M2) : M2 := ⟨A.d, -A.b, -A.c, A.a⟩

theorem mul_adj (A : M2) : A * adj A = ⟨M2.det A, 0, 0, M2.det A⟩ := by
  sorry

theorem inverse (A : M2) (h : M2.det A = 1) : A * adj A = M2.id2 ∧ adj A * A = M2.id2 := by
  sorry

end Parcours.Matrices

#verifier
