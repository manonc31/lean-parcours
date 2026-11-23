import Exercices.Circuits.Definitions

/-!
# La porte NAND est universelle

Une seule porte logique suffit pour fabriquer **tous** les circuits : la porte NAND
(« non-et » : `nand a b = !(a && b)`). Les puces électroniques sont d'ailleurs construites
presque uniquement avec des NAND (ou des NOR).

## À prouver
Que les circuits construits avec des NAND calculent bien NON, ET, OU et OU exclusif.

## Ressources
- [Fonction NON-ET (Wikipédia)](https://fr.wikipedia.org/wiki/Fonction_NON-ET)

---
*Exercice* `Circuits.Nand` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Circuits.Nand` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Circuits

def nand (a b : Bool) : Bool := !(a && b)

def non (a : Bool) : Bool := nand a a
def et (a b : Bool) : Bool := nand (nand a b) (nand a b)
def ou (a b : Bool) : Bool := nand (nand a a) (nand b b)
def ouex (a b : Bool) : Bool := nand (nand a (nand a b)) (nand b (nand a b))

theorem non_ok (a : Bool) : non a = !a := by
  sorry

theorem et_ok (a b : Bool) : et a b = (a && b) := by
  sorry

theorem ou_ok (a b : Bool) : ou a b = (a || b) := by
  sorry

theorem ouex_ok (a b : Bool) : ouex a b = xor a b := by
  sorry

end Parcours.Circuits

#verifier
