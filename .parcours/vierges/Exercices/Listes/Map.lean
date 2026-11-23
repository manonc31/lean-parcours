import Exercices.Listes.Miroir

/-!
# Appliquer une fonction à chaque élément : `map`

`map f [a, b, c] = [f a, f b, f c]`. C'est le `map` de tous les langages fonctionnels.

## À prouver
1. `map_concat : map f (l₁ ++ l₂) = map f l₁ ++ map f l₂`
2. `map_map : map g (map f l) = map (g ∘ f) l`
3. `longueur_map : longueur (map f l) = longueur l`
4. `map_miroir : map f (miroir l) = miroir (map f l)`

---
*Exercice* `Listes.Map` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Listes.Map` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Listes.Liste

variable {α β γ : Type}

theorem map_concat (f : α → β) (l₁ l₂ : Liste α) : map f (l₁ ++ l₂) = map f l₁ ++ map f l₂ := by
  sorry

theorem map_map (f : α → β) (g : β → γ) (l : Liste α) : map g (map f l) = map (g ∘ f) l := by
  sorry

theorem longueur_map (f : α → β) (l : Liste α) : longueur (map f l) = longueur l := by
  sorry

theorem map_miroir (f : α → β) (l : Liste α) : map f (miroir l) = miroir (map f l) := by
  sorry

end Parcours.Listes.Liste

#verifier
