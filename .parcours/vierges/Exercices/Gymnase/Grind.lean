import Exercices.Naturels.Carre
import Exercices.Logique.Bilan
import Exercices.Naturels.Transfert

/-!
# La tactique grind

Depuis l'identité remarquable, **`grind`** est débloqué. C'est un « couteau suisse » : il combine calcul algébrique (anneaux), arithmétique linéaire, et raisonnement sur les égalités.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.Grind` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Gymnase.Grind` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem grind1 (a b : Nat) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by
  sorry

theorem grind2 (x y : Int) (h : x = y + 1) : x * x - y * y = 2 * y + 1 := by
  sorry

end Parcours.Gymnase

#verifier
