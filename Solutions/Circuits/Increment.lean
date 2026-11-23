/- @parcours
titre: Le compteur binaire
difficulte: 2
requiert: Circuits.VersBinaire
indice: Récurrence sur `l`, puis `cases b` sur le premier bit.
indice: `valeur_cons : valeur (b :: l) = b.toNat + 2 * valeur l`.
-/
import Solutions.Circuits.Definitions

/-!
# Le compteur binaire

Ajouter 1 en binaire : on parcourt les bits depuis le poids faible ; les `1` deviennent des `0`
(c'est la retenue qui se propage) jusqu'au premier `0`, qui devient `1`.
`[true, true, false, true]` (= 11) devient `[false, false, true, true]` (= 12).

## À prouver
1. `incr_valeur : valeur (incr l) = valeur l + 1`
2. `incr_longueur` : la longueur augmente d'au plus 1.
-/

namespace Parcours.Circuits

def incr : List Bool → List Bool
  | [] => [true]
  | false :: l => true :: l
  | true :: l => false :: incr l

theorem incr_valeur (l : List Bool) : valeur (incr l) = valeur l + 1 := by -- @exo
  induction l with
  | nil => rfl
  | cons b l ih =>
    cases b
    · simp [incr, valeur_cons]
      omega
    · simp [incr, valeur_cons, ih]
      omega

theorem incr_longueur (l : List Bool) : (incr l).length ≤ l.length + 1 := by -- @exo
  induction l with
  | nil => simp [incr]
  | cons b l ih =>
    cases b
    · simp [incr]
    · simp [incr]
      omega

end Parcours.Circuits

#verifier
