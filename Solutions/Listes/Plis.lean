/- @parcours
titre: Les plis (fold)
difficulte: 3
indice: `somme_concat` : récurrence sur `l₁`, puis `omega` pour réarranger.
indice: `foldl_miroir` : il faut une version généralisée : `induction l generalizing b`. Tu auras besoin d'un lemme sur `foldr f b (l₁ ++ l₂)` : prouve-le d'abord dans un `have`, ou utilise `foldr_concat`.
indice: `foldr_concat : foldr f b (l₁ ++ l₂) = foldr f (foldr f b l₂) l₁` se prouve par récurrence sur `l₁`.
-/
import Solutions.Listes.Miroir

/-!
# Les plis (fold)

`foldr f b [x₁, x₂, x₃] = f x₁ (f x₂ (f x₃ b))` (plier par la droite)
`foldl f b [x₁, x₂, x₃] = f (f (f b x₁) x₂) x₃` (plier par la gauche)

Presque toute fonction sur les listes est un pli : la somme, la longueur, le maximum…

## À prouver
1. `somme_concat : somme (l₁ ++ l₂) = somme l₁ + somme l₂`
2. `foldr_concat : foldr f b (l₁ ++ l₂) = foldr f (foldr f b l₂) l₁`
3. `foldl_miroir : foldl f b l = foldr (fun x acc => f acc x) b (miroir l)`
-/

namespace Parcours.Listes.Liste

variable {α β : Type}

theorem somme_concat (l₁ l₂ : Liste Nat) : somme (l₁ ++ l₂) = somme l₁ + somme l₂ := by -- @exo
  induction l₁ with
  | nil => exact (Nat.zero_add _).symm
  | cons x l ih =>
    show x + somme (l ++ l₂) = x + somme l + somme l₂
    rw [ih]
    omega

theorem foldr_concat (f : α → β → β) (b : β) (l₁ l₂ : Liste α) :
    foldr f b (l₁ ++ l₂) = foldr f (foldr f b l₂) l₁ := by -- @exo
  induction l₁ with
  | nil => rfl
  | cons x l ih =>
    show f x (foldr f b (l ++ l₂)) = f x (foldr f (foldr f b l₂) l)
    rw [ih]

theorem foldl_miroir (f : β → α → β) (b : β) (l : Liste α) :
    foldl f b l = foldr (fun x acc => f acc x) b (miroir l) := by -- @exo
  induction l generalizing b with
  | nil => rfl
  | cons x l ih =>
    show foldl f (f b x) l = _
    rw [ih, miroir_cons, foldr_concat]
    rfl

end Parcours.Listes.Liste

#verifier
