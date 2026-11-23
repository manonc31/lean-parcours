/- @parcours
titre: Le castor affairé
difficulte: 2
requiert: Informatique.Arret
indice: Des simulations : `decide`.
indice: Essaie `#eval executer castor2 3 ruban |>.map (·.1)` pour suivre la machine pas à pas.
-/
import Solutions.Listes.Pont
import Solutions.Recurrence.Definitions

/-!
# Le castor affairé

Parmi toutes les machines de Turing à `n` états qui **s'arrêtent** (en partant d'un ruban vide),
laquelle écrit le plus de `1` ? C'est le problème du **castor affairé** (Tibor Radó, 1962). Pour
2 états, le champion écrit 4 uns en 6 étapes ; pour 3 états, 6 uns. Pour 5 états, la réponse
(47 176 870 étapes) n'a été prouvée qu'en 2024… en Coq, un cousin de Lean ! Pour 6 états, le
problème est hors de portée : la fonction du castor affairé grandit plus vite que toute fonction
calculable.

## À prouver
1. `castor_deux` : la machine à 2 états s'arrête après 6 étapes avec 4 uns.
2. `castor_trois` : une machine à 3 états qui écrit 6 uns en 14 étapes.
3. `castor_trois_lent` : une autre qui s'arrête après 21 étapes (le record de durée pour 3 états).

## Ressources
- [Castor affairé (Wikipédia)](https://fr.wikipedia.org/wiki/Castor_affair%C3%A9)
- [Le projet bbchallenge (BB(5), 2024)](https://bbchallenge.org/)
-/

namespace Parcours.Info

structure Regle where
  ecrit : Bool
  versDroite : Bool
  suivant : Nat

/-- Une machine : (état, symbole lu) ↦ règle. L'état 0 est l'arrêt. -/
abbrev Machine := Nat → Bool → Regle

structure Config where
  etat : Nat
  gauche : List Bool
  tete : Bool
  droite : List Bool

def unPas (M : Machine) (c : Config) : Config :=
  let r := M c.etat c.tete
  if r.versDroite then ⟨r.suivant, r.ecrit :: c.gauche, c.droite.headD false, c.droite.tail⟩
  else ⟨r.suivant, c.gauche.tail, c.gauche.headD false, r.ecrit :: c.droite⟩

/-- Nombre d'étapes et configuration finale (si la machine s'arrête avant `f` étapes). -/
def executer (M : Machine) : Nat → Config → Option (Nat × Config)
  | 0, _ => none
  | f + 1, c => if c.etat = 0 then some (0, c) else (executer M f (unPas M c)).map fun r => (r.1 + 1, r.2)

def nbUns (c : Config) : Nat := c.gauche.count true + c.tete.toNat + c.droite.count true

def ruban : Config := ⟨1, [], false, []⟩

def bilan (M : Machine) : Option (Nat × Nat) := (executer M 100 ruban).map fun r => (r.1, nbUns r.2)

def castor2 : Machine
  | 1, false => ⟨true, true, 2⟩
  | 1, true => ⟨true, false, 2⟩
  | 2, false => ⟨true, false, 1⟩
  | 2, true => ⟨true, true, 0⟩
  | _, _ => ⟨false, true, 0⟩

def castor3 : Machine
  | 1, false => ⟨true, true, 2⟩
  | 1, true => ⟨true, true, 0⟩
  | 2, false => ⟨false, true, 3⟩
  | 2, true => ⟨true, true, 2⟩
  | 3, false => ⟨true, false, 3⟩
  | 3, true => ⟨true, false, 1⟩
  | _, _ => ⟨false, true, 0⟩

def castor3lent : Machine
  | 1, false => ⟨true, true, 2⟩
  | 1, true => ⟨true, true, 0⟩
  | 2, false => ⟨true, false, 2⟩
  | 2, true => ⟨false, true, 3⟩
  | 3, false => ⟨true, false, 3⟩
  | 3, true => ⟨true, false, 1⟩
  | _, _ => ⟨false, true, 0⟩

theorem castor_deux : bilan castor2 = some (6, 4) := by -- @exo
  decide

theorem castor_trois : bilan castor3 = some (14, 6) := by -- @exo
  decide

theorem castor_trois_lent : bilan castor3lent = some (21, 5) := by -- @exo
  decide

end Parcours.Info

#verifier
