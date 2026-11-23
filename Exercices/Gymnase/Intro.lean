import ParcoursOutils

/-!
# Introduire des hypothèses

Pour prouver `P → Q → P`, `intro hp hq` introduit les deux hypothèses ; il reste à prouver `P`.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.Intro` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Gymnase.Intro` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem intro_exemple (P Q : Prop) : P → Q → P := by
  sorry

end Parcours.Gymnase

#verifier
