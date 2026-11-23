import ParcoursOutils

/-!
# Échanger les hypothèses

Une fonction de deux arguments peut prendre ses arguments dans l'autre ordre.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.Echange` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Gymnase.Echange` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem echange (P Q R : Prop) : (P → Q → R) → (Q → P → R) := by
  sorry

end Parcours.Gymnase

#verifier
