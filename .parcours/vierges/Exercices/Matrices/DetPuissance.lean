import Exercices.Matrices.Determinant

/-!
# Déterminant d'une puissance

`det(Aⁿ) = (det A)ⁿ`. Appliqué à la matrice de Fibonacci (de déterminant −1), on retrouve
l'identité de Cassini !

## À prouver
`det_puiss (A : M2) (n : Nat) : M2.det (M2.puiss A n) = M2.det A ^ n`

---
*Exercice* `Matrices.DetPuissance` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Matrices.DetPuissance` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Matrices

theorem det_puiss (A : M2) (n : Nat) : M2.det (M2.puiss A n) = M2.det A ^ n := by
  sorry

end Parcours.Matrices

#verifier
