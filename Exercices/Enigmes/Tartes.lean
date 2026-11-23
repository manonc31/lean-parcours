import Exercices.Logique.Bilan
import Exercices.Listes.Pont

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

---
*Exercice* `Enigmes.Tartes` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Enigmes.Tartes` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Enigmes

/-- Les déclarations sont-elles cohérentes si le voleur est `x` ? -/
def coherent (x : Nat) : Bool :=
  let lievre := x != 2
  let chapelier := x == 0
  let loir := !chapelier
  (lievre == (x != 0)) && (chapelier == (x != 1)) && (loir == (x != 2))

theorem voleur : ∀ x, x < 3 → (coherent x = true ↔ x = 1) := by
  sorry

end Parcours.Enigmes

#verifier
