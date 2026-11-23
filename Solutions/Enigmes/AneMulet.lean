/- @parcours
titre: L'âne et le mulet
difficulte: 1
requiert: Enigmes.PoulesLapins
indice: `omega`, même avec des soustractions (tronquées) sur `Nat`.
-/
import Solutions.Recurrence.Definitions

/-!
# L'âne et le mulet

Une énigme attribuée à Euclide : un âne et un mulet portent des sacs. L'âne se plaint de sa
charge. Le mulet lui dit : « Si tu me donnais un de tes sacs, j'en porterais deux fois plus que
toi ; si je t'en donnais un des miens, nous en porterions autant. » Combien portent-ils ?

## À prouver
`ane_mulet : m + 1 = 2 * (a - 1) → m - 1 = a + 1 → a = 5 ∧ m = 7`
-/

namespace Parcours.Enigmes

theorem ane_mulet (a m : Nat) (h1 : m + 1 = 2 * (a - 1)) (h2 : m - 1 = a + 1) :
    a = 5 ∧ m = 7 := by -- @exo
  omega

end Parcours.Enigmes

#verifier
