import ParcoursOutils

/-!
# Plusieurs quantificateurs

`intro a b h` introduit d'un coup tous les `∀` et les hypothèses.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.ImbriquesIntro` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Gymnase.ImbriquesIntro` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem imbriques : ∀ a b : Nat, a = b → b = a := by
  sorry

end Parcours.Gymnase

#verifier
