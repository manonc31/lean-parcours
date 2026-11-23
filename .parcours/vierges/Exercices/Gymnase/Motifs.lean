import ParcoursOutils

/-!
# Introduire avec un motif

`rintro ⟨x, hp, hq⟩` introduit une hypothèse `∃ x, P x ∧ Q x` et la découpe d'un coup.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.Motifs` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Gymnase.Motifs` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem motif (P Q : Nat → Prop) : (∃ x, P x ∧ Q x) → ∃ x, Q x := by
  sorry

end Parcours.Gymnase

#verifier
