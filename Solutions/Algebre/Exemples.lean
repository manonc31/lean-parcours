/- @parcours
titre: Des exemples de groupes
difficulte: 2
indice: Pour `Bool` avec le « ou exclusif » : chaque axiome porte sur un nombre fini de cas, `decide` les vérifie.
indice: Pour les entiers relatifs avec l'addition : chaque champ se prouve avec `omega` (après avoir déplié, par exemple `show (a + b) + c = a + (b + c)`).
indice: Puis tu peux appliquer tes théorèmes : `commutatif_si_carre_un` marche pour `Bool` !
-/
import Solutions.Algebre.Exposant2
import Solutions.Naturels.Transfert

/-!
# Des exemples de groupes

Construis deux groupes concrets en donnant leurs opérations et en prouvant les axiomes :
1. `Bool` avec le « ou exclusif » (`xor`), neutre `false`, et chaque élément son propre inverse.
2. Les entiers relatifs `Int` avec l'**addition** (on l'enveloppe dans une structure `Additif`
   pour pouvoir noter l'addition `*`).

Puis profite : tous tes théorèmes s'appliquent automatiquement.

## À faire
1. `instance groupeBool : Groupe Bool`
2. `instance groupeAdditif : Groupe Additif`
3. `bool_commutatif : ∀ a b : Bool, a * b = b * a` (sans calcul : utilise ton théorème sur `x * x = 1` !)
-/

namespace Parcours.Algebre

instance groupeBool : Groupe Bool := -- @exo
  { mul := xor
    one := false
    inv := id
    mul_assoc := by decide
    one_mul := by decide
    inv_mul := by decide }

/-- Les entiers relatifs, vus avec l'addition. -/
structure Additif where
  val : Int

instance groupeAdditif : Groupe Additif := -- @exo
  { mul := fun a b => ⟨a.val + b.val⟩
    one := ⟨0⟩
    inv := fun a => ⟨-a.val⟩
    mul_assoc := fun a b c => by
      show Additif.mk (a.val + b.val + c.val) = Additif.mk (a.val + (b.val + c.val))
      rw [Int.add_assoc]
    one_mul := fun a => by
      show Additif.mk (0 + a.val) = a
      rw [Int.zero_add]
    inv_mul := fun a => by
      show Additif.mk (-a.val + a.val) = Additif.mk 0
      rw [Int.add_left_neg] }

theorem bool_commutatif (a b : Bool) : a * b = b * a := by -- @exo
  apply commutatif_si_carre_un
  decide

end Parcours.Algebre

#verifier
