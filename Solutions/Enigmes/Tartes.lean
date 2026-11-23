/- @parcours
titre: Qui a volé les tartes ?
difficulte: 1
requiert: Enigmes.Chevaliers
indice: `decide` essaie les trois suspects.
-/
import Solutions.Logique.Bilan
import Solutions.Listes.Pont

/-!
# Qui a volé les tartes ?

Au pays d'Alice, les tartes de la Reine ont disparu. Trois suspects : le Lièvre de Mars (0), le
Chapelier (1) et le Loir (2). Un seul est coupable. Le coupable ment, les innocents disent la
vérité.
- Le Lièvre : « Le Loir est innocent. »
- Le Chapelier : « C'est le Lièvre qui a volé les tartes. »
- Le Loir : « Le Chapelier ment. »

Qui est le voleur ?

## À prouver
`voleur` : seul le Chapelier est compatible avec les déclarations.
-/

namespace Parcours.Enigmes

/-- Les déclarations sont-elles cohérentes si le voleur est `x` ? -/
def coherent (x : Nat) : Bool :=
  let lievre := x != 2
  let chapelier := x == 0
  let loir := !chapelier
  (lievre == (x != 0)) && (chapelier == (x != 1)) && (loir == (x != 2))

theorem voleur : ∀ x, x < 3 → (coherent x = true ↔ x = 1) := by -- @exo
  decide

end Parcours.Enigmes

#verifier
