import ParcoursOutils

/-!
# Découper un « et » triple

`P ∧ Q ∧ R` se lit `P ∧ (Q ∧ R)`. `obtain ⟨hp, hq, hr⟩ := h` découpe tout d'un coup.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.Obtain` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Gymnase.Obtain` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem obtain_exemple (P Q R : Prop) (h : P ∧ Q ∧ R) : R := by
  sorry

end Parcours.Gymnase

#verifier
