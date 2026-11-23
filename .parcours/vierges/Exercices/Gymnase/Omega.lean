import Exercices.Naturels.Transfert

/-!
# La tactique omega

Depuis le Pont des entiers, la tactique **`omega`** est débloquée : elle résout toute seule les problèmes d'arithmétique **linéaire** (+, −, ≤, <, multiplication par une constante) sur `Nat` et `Int`.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.Omega` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Gymnase.Omega` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem omega1 (a b : Nat) (h : a < b) : a + 1 ≤ b := by
  sorry

theorem omega2 (x y : Nat) (h1 : x + y = 10) (h2 : x = y + 2) : x = 6 := by
  sorry

end Parcours.Gymnase

#verifier
