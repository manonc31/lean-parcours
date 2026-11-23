import ParcoursOutils

/-!
# Choisir un côté

Pour prouver `P ∨ (Q ∨ R)` à partir de `Q` : `right` puis `left`.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.Gauche` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Gymnase.Gauche` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem gauche_droite (P Q R : Prop) (hq : Q) : P ∨ Q ∨ R := by
  sorry

end Parcours.Gymnase

#verifier
