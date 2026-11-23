import Exercices.Naturels.Transfert

/-!
# Prouver une équivalence

Pour `P ↔ Q` : `constructor`, puis les deux sens.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.Equivalence` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Gymnase.Equivalence` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem equivalence_exemple (n : Nat) : n = 0 ↔ n + 1 = 1 := by
  sorry

end Parcours.Gymnase

#verifier
