import Exercices.Listes.Map

/-!
# Appartenance

`x ∈ l` est défini inductivement : `x` est la tête, ou bien `x` est dans la queue.
Le lemme `mem_cons : x ∈ y ∷ l ↔ x = y ∨ x ∈ l` (dans le cours) est ton meilleur ami.

## À prouver
1. `mem_concat : x ∈ l₁ ++ l₂ ↔ x ∈ l₁ ∨ x ∈ l₂`
2. `mem_miroir : x ∈ miroir l ↔ x ∈ l`
3. `mem_map : y ∈ map f l ↔ ∃ x, x ∈ l ∧ f x = y`

---
*Exercice* `Listes.Appartenance` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Listes.Appartenance` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Listes.Liste

variable {α β : Type}

theorem mem_concat (x : α) (l₁ l₂ : Liste α) : x ∈ l₁ ++ l₂ ↔ x ∈ l₁ ∨ x ∈ l₂ := by
  sorry

theorem mem_miroir (x : α) (l : Liste α) : x ∈ miroir l ↔ x ∈ l := by
  sorry

theorem mem_map (f : α → β) (y : β) (l : Liste α) : y ∈ map f l ↔ ∃ x, x ∈ l ∧ f x = y := by
  sorry

end Parcours.Listes.Liste

#verifier
