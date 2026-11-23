import Exercices.Circuits.Definitions

/-!
# Le compteur binaire

Ajouter 1 en binaire : on parcourt les bits depuis le poids faible ; les `1` deviennent des `0`
(c'est la retenue qui se propage) jusqu'au premier `0`, qui devient `1`.
`[true, true, false, true]` (= 11) devient `[false, false, true, true]` (= 12).

## À prouver
1. `incr_valeur : valeur (incr l) = valeur l + 1`
2. `incr_longueur` : la longueur augmente d'au plus 1.

---
*Exercice* `Circuits.Increment` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Circuits.Increment` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Circuits

def incr : List Bool → List Bool
  | [] => [true]
  | false :: l => true :: l
  | true :: l => false :: incr l

theorem incr_valeur (l : List Bool) : valeur (incr l) = valeur l + 1 := by
  sorry

theorem incr_longueur (l : List Bool) : (incr l).length ≤ l.length + 1 := by
  sorry

end Parcours.Circuits

#verifier
