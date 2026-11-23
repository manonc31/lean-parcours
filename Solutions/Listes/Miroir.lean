/- @parcours
titre: Le miroir
difficulte: 2
indice: `miroir_concat` : récurrence sur `l₁`. Cas `nil` : `concat_nil`. Cas `cons` : `rw [cons_concat, miroir_cons, miroir_cons, ih, concat_assoc]`.
indice: `miroir_miroir` : récurrence ; cas `cons` : `rw [miroir_cons, miroir_concat, ih]` puis il reste quelque chose de vrai par définition.
-/
import Solutions.Listes.ConcatNil
import Solutions.Listes.ConcatAssoc

/-!
# Le miroir

Renverser deux fois une liste redonne la liste de départ. Pour le prouver, il faut d'abord
comprendre comment le miroir interagit avec la concaténation.

## À prouver
1. `miroir_concat (l₁ l₂ : Liste α) : miroir (l₁ ++ l₂) = miroir l₂ ++ miroir l₁`
2. `miroir_miroir (l : Liste α) : miroir (miroir l) = l`
-/

namespace Parcours.Listes.Liste

variable {α : Type}

theorem miroir_concat (l₁ l₂ : Liste α) : miroir (l₁ ++ l₂) = miroir l₂ ++ miroir l₁ := by -- @exo
  induction l₁ with
  | nil => rw [nil_concat, miroir_nil, concat_nil]
  | cons x l ih => rw [cons_concat, miroir_cons, miroir_cons, ih, concat_assoc]

theorem miroir_miroir (l : Liste α) : miroir (miroir l) = l := by -- @exo
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [miroir_cons, miroir_concat, ih]
    rfl

end Parcours.Listes.Liste

#verifier
