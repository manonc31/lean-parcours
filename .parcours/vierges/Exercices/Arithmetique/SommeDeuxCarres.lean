import Exercices.Arithmetique.Definitions

/-!
# Somme de deux carrés modulo 4

Une somme de deux carrés n'est jamais de la forme `4k + 3`. Donc `3, 7, 11, 19, 23…` ne sont pas sommes
de deux carrés. (Fermat a montré que pour les premiers, c'est même une équivalence : voir le boss des deux carrés.)

## À prouver
`somme_deux_carres (a b : Nat) : (a * a + b * b) % 4 ≠ 3`

---
*Exercice* `Arithmetique.SommeDeuxCarres` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Arithmetique.SommeDeuxCarres` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Arith

theorem somme_deux_carres (a b : Nat) : (a * a + b * b) % 4 ≠ 3 := by
  sorry

end Parcours.Arith

#verifier
