import Exercices.Listes.Miroir

/-!
# Les plis (fold)

`foldr f b [x₁, x₂, x₃] = f x₁ (f x₂ (f x₃ b))` (plier par la droite)
`foldl f b [x₁, x₂, x₃] = f (f (f b x₁) x₂) x₃` (plier par la gauche)

Presque toute fonction sur les listes est un pli : la somme, la longueur, le maximum…

## À prouver
1. `somme_concat : somme (l₁ ++ l₂) = somme l₁ + somme l₂`
2. `foldr_concat : foldr f b (l₁ ++ l₂) = foldr f (foldr f b l₂) l₁`
3. `foldl_miroir : foldl f b l = foldr (fun x acc => f acc x) b (miroir l)`

---
*Exercice* `Listes.Plis` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Listes.Plis` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Listes.Liste

variable {α β : Type}

theorem somme_concat (l₁ l₂ : Liste Nat) : somme (l₁ ++ l₂) = somme l₁ + somme l₂ := by
  sorry

theorem foldr_concat (f : α → β → β) (b : β) (l₁ l₂ : Liste α) :
    foldr f b (l₁ ++ l₂) = foldr f (foldr f b l₂) l₁ := by
  sorry

theorem foldl_miroir (f : β → α → β) (b : β) (l : Liste α) :
    foldl f b l = foldr (fun x acc => f acc x) b (miroir l) := by
  sorry

end Parcours.Listes.Liste

#verifier
