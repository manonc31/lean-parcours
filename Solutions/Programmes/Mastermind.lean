/- @parcours
titre: Mastermind
difficulte: 1
requiert: Programmes.Compter
indice: `exemple` : `decide`.
indice: `bienPlaces_le` : `List.count_le_length` et `List.length_zipWith` (la longueur est le minimum des deux).
indice: `bienPlaces_comm` : `List.zipWith_comm` échange les deux listes.
-/
import Solutions.Programmes.Definitions

/-!
# Mastermind

Au Mastermind, un joueur cache une combinaison de 4 couleurs (parmi 6) ; l'autre propose des
combinaisons et reçoit deux indices : le nombre de pions **bien placés**, et le nombre de pions
de la bonne couleur mais **mal placés**.

## À prouver
1. `exemple_mastermind` : pour le secret `[1, 2, 3, 4]` et la proposition `[1, 3, 2, 5]` : 1 bien placé, 2 mal placés.
2. `bienPlaces_le` : il y a au plus autant de bien placés que de pions.
3. `bienPlaces_comm` : l'indice « bien placés » est symétrique.

## Ressources
- [Mastermind (Wikipédia)](https://fr.wikipedia.org/wiki/Mastermind)
-/

namespace Parcours.Prog

def bienPlaces (s g : List Nat) : Nat := (List.zipWith (· == ·) s g).count true

def communs (s g : List Nat) : Nat := ((List.range 6).map fun c => min (s.count c) (g.count c)).sum

def malPlaces (s g : List Nat) : Nat := communs s g - bienPlaces s g

theorem exemple_mastermind : bienPlaces [1, 2, 3, 4] [1, 3, 2, 5] = 1 ∧ malPlaces [1, 2, 3, 4] [1, 3, 2, 5] = 2 := by -- @exo
  decide

theorem bienPlaces_le (s g : List Nat) : bienPlaces s g ≤ s.length := by -- @exo
  unfold bienPlaces
  have h1 := List.count_le_length (a := true) (l := List.zipWith (· == ·) s g)
  rw [List.length_zipWith] at h1
  omega

theorem bienPlaces_comm (s g : List Nat) : bienPlaces s g = bienPlaces g s := by -- @exo
  unfold bienPlaces
  rw [List.zipWith_comm]
  congr 2
  funext a b
  exact Bool.beq_comm

end Parcours.Prog

#verifier
