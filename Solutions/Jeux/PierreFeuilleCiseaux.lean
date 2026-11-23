/- @parcours
titre: Pierre-feuille-ciseaux
difficulte: 2
requiert: Jeux.Nash
indice: Pour `pas_de_nash_pur` : `intro a b` puis `decide` (il n'y a que 9 cas !). Il faut d'abord que `Nash3 a b` soit décidable : c'est fourni.
-/
import Solutions.Jeux.Nash

/-!
# Pierre-feuille-ciseaux

À pierre-feuille-ciseaux, il n'y a **aucun équilibre de Nash « pur »** : quelle que soit la paire
de coups, l'un des deux joueurs aurait mieux fait de jouer autre chose. Le seul équilibre est
de jouer **au hasard** (1/3 chacun) — d'où l'importance des stratégies mixtes en théorie des jeux.

`gain a b` : 1 si `a` bat `b`, 0 sinon.

## À prouver
1. `pas_de_nash_pur : ∀ a b, ¬Nash3 a b`
2. `cycle` : la pierre bat les ciseaux, qui battent la feuille, qui bat la pierre.
-/

namespace Parcours.Jeux

inductive Coup where
  | pierre | feuille | ciseaux
  deriving DecidableEq, Repr

open Coup

def bat : Coup → Coup → Bool
  | pierre, ciseaux => true
  | ciseaux, feuille => true
  | feuille, pierre => true
  | _, _ => false

def gain (a b : Coup) : Nat := if bat a b then 1 else 0

def tous : List Coup := [pierre, feuille, ciseaux]

/-- Équilibre de Nash : aucun joueur ne gagne plus en changeant seul de coup. -/
def Nash3 (a b : Coup) : Prop := (∀ a' ∈ tous, gain a' b ≤ gain a b) ∧ (∀ b' ∈ tous, gain b' a ≤ gain b a)

instance (a b : Coup) : Decidable (Nash3 a b) := by unfold Nash3; infer_instance

theorem pas_de_nash_pur (a b : Coup) : ¬Nash3 a b := by -- @exo
  cases a <;> cases b <;> decide

theorem cycle : bat pierre ciseaux ∧ bat ciseaux feuille ∧ bat feuille pierre := by -- @exo
  decide

end Parcours.Jeux

#verifier
