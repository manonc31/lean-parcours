/- @parcours
titre: Demi-additionneur et additionneur complet
difficulte: 1
indice: Il n'y a que 4 (ou 8) combinaisons d'entrées : `cases a <;> cases b <;> rfl` (et `cases c` en plus pour l'additionneur complet).
-/
import Solutions.Circuits.Definitions

/-!
# Demi-additionneur et additionneur complet

Le **demi-additionneur** additionne deux bits : la somme est `a xor b`, la retenue `a && b`.
L'**additionneur complet** additionne trois bits (dont une retenue entrante) avec deux
demi-additionneurs et une porte OU. C'est la brique de base de tous les processeurs.

## À prouver
1. `demi_additionneur : a.toNat + b.toNat = (xor a b).toNat + 2 * (a && b).toNat`
2. `additionneur_complet : a.toNat + b.toNat + c.toNat = (somme a b c).toNat + 2 * (retenue a b c).toNat`
-/

namespace Parcours.Circuits

def somme (a b c : Bool) : Bool := xor (xor a b) c
def retenue (a b c : Bool) : Bool := (a && b) || (xor a b && c)

theorem demi_additionneur (a b : Bool) :
    a.toNat + b.toNat = (xor a b).toNat + 2 * (a && b).toNat := by -- @exo
  cases a <;> cases b <;> rfl

theorem additionneur_complet (a b c : Bool) :
    a.toNat + b.toNat + c.toNat = (somme a b c).toNat + 2 * (retenue a b c).toNat := by -- @exo
  cases a <;> cases b <;> cases c <;> rfl

end Parcours.Circuits

#verifier
