import ParcoursOutils

/-!
# Construire un « et »

`constructor` découpe le but `A ∧ B` en deux buts `A` et `B`. Traite-les avec `·` (tapé `\.`).

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.Constructor` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Gymnase.Constructor` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem constructor_exemple (P Q : Prop) (hp : P) (hq : Q) : Q ∧ P := by
  sorry

end Parcours.Gymnase

#verifier
