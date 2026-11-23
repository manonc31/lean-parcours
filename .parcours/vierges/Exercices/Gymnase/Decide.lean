import ParcoursOutils

/-!
# Faire vérifier par la machine

Pour un énoncé **sans variable** qui se vérifie par calcul (égalités, inégalités, `≠` sur des nombres…), `decide` fait le calcul et conclut.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.Decide` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Gymnase.Decide` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem decide_ne : (2 : Nat) ≠ 3 := by
  sorry

theorem decide_reste : (17 : Nat) % 5 = 2 := by
  sorry

theorem decide_ou : (10 : Nat) < 3 ∨ 2 ≤ 2 := by
  sorry

end Parcours.Gymnase

#verifier
