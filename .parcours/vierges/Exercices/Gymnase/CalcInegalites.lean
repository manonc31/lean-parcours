import Exercices.Naturels.Transfert

/-!
# calc avec des inégalités

`calc` marche aussi avec `≤` et `<` : chaque étape peut être `=`, `≤` ou `<`, et Lean combine.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.CalcInegalites` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Gymnase.CalcInegalites` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem calc_ineg (a b c : Nat) (h1 : a ≤ b) (h2 : b < c) : a + 1 < c + 1 := by
  sorry

end Parcours.Gymnase

#verifier
