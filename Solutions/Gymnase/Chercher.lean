/- @parcours
titre: Chercher un lemme avec exact?
difficulte: 1
requiert: Gymnase.Omega
indice: Écris `exact?` et regarde la suggestion dans l'infoview.
indice: Il trouve `Nat.mul_comm a b`.
-/
import Solutions.Naturels.Transfert

/-!
# Chercher un lemme avec exact?

`exact?` **cherche** dans la bibliothèque un lemme qui prouve le but, et te propose la ligne à écrire (clique dessus dans l'infoview). Ici, après le Pont, les lemmes de `Nat` sont permis.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem chercher (a b : Nat) : a * b = b * a := by -- @exo
  exact Nat.mul_comm a b

end Parcours.Gymnase

#verifier
