/- @parcours
titre: Tables de vérité
difficulte: 1
requiert: Logique.Et
indice: `cases a <;> cases b <;> rfl` essaie toutes les valeurs.
indice: Pour une équivalence : `revert a b` puis `decide`.
-/
import ParcoursOutils

/-!
# Tables de vérité

En Lean il y a deux mondes : les **propositions** (`Prop`, ce qu'on prouve) et les **booléens**
(`Bool`, ce qu'on calcule). `&&`, `||`, `!` sont les versions calculables de `∧`, `∨`, `¬`.
Comme un booléen n'a que deux valeurs, une égalité de booléens se vérifie en essayant tous les cas :
c'est la méthode des **tables de vérité**.

## À prouver
1. `de_morgan_bool : !(a && b) = (!a || !b)`
2. `distrib_bool : (a && (b || c)) = ((a && b) || (a && c))`
3. `et_vrai_iff : (a && b) = true ↔ a = true ∧ b = true`
-/

namespace Parcours.Logique

theorem de_morgan_bool (a b : Bool) : (!(a && b)) = (!a || !b) := by -- @exo
  cases a <;> cases b <;> rfl

theorem distrib_bool (a b c : Bool) : (a && (b || c)) = ((a && b) || (a && c)) := by -- @exo
  cases a <;> cases b <;> cases c <;> rfl

theorem et_vrai_iff (a b : Bool) : (a && b) = true ↔ a = true ∧ b = true := by -- @exo
  revert a b
  decide

end Parcours.Logique

#verifier
