import Exercices.Naturels.Transfert

/-!
# Les limites d'omega

`omega` ne comprend pas la multiplication de deux **variables** (`a * b`) : il la traite comme une boîte noire. Ici, il faut d'abord établir un fait sur `a * b` avec un lemme (`Nat.mul_le_mul`), puis laisser `omega` finir.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.OmegaLimites` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Gymnase.OmegaLimites` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem omega_limite (a b : Nat) (ha : 2 ≤ a) (hb : 3 ≤ b) : 6 ≤ a * b + 0 := by
  sorry

end Parcours.Gymnase

#verifier
