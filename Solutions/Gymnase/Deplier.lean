/- @parcours
titre: Déplier une définition
difficulte: 2
requiert: Gymnase.Grind
indice: `unfold carre` puis `rfl`.
indice: Pour le second : `unfold carre` puis `grind`.
-/
import Solutions.Naturels.Carre
import Solutions.Logique.Bilan
import Solutions.Naturels.Transfert

/-!
# Déplier une définition

`unfold carre` remplace `carre` par sa définition dans le but. Utile quand `rw` ou `simp` ne voient pas à travers une définition.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

def carre (n : Nat) : Nat := n * n

theorem carre_trois : carre 3 = 9 := by -- @exo
  unfold carre
  rfl

theorem carre_succ (n : Nat) : carre (n + 1) = carre n + 2 * n + 1 := by -- @exo
  unfold carre
  grind

end Parcours.Gymnase

#verifier
