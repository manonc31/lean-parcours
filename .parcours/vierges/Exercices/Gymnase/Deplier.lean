import Exercices.Naturels.Carre
import Exercices.Logique.Bilan
import Exercices.Naturels.Transfert

/-!
# Déplier une définition

`unfold carre` remplace `carre` par sa définition dans le but. Utile quand `rw` ou `simp` ne voient pas à travers une définition.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.Deplier` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Gymnase.Deplier` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

def carre (n : Nat) : Nat := n * n

theorem carre_trois : carre 3 = 9 := by
  sorry

theorem carre_succ (n : Nat) : carre (n + 1) = carre n + 2 * n + 1 := by
  sorry

end Parcours.Gymnase

#verifier
