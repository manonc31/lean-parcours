import ParcoursOutils

/-!
# Raisonner par cas

`rcases h with hp | hq` crée deux buts : un où `P` est vrai, un où `Q` est vrai.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.Rcases` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Gymnase.Rcases` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem rcases_exemple (P Q R : Prop) (h : P ∨ Q) (hpr : P → R) (hqr : Q → R) : R := by
  sorry

end Parcours.Gymnase

#verifier
