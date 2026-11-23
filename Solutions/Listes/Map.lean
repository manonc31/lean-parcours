/- @parcours
titre: Appliquer une fonction à une liste
difficulte: 2
indice: Toutes les preuves : récurrence sur `l` (ou `l₁`), puis `rw` avec `map_cons`, `cons_concat`, `ih`…
indice: `map_miroir` : tu auras besoin de `map_concat` (que tu viens de prouver !).
-/
import Solutions.Listes.Miroir

/-!
# Appliquer une fonction à chaque élément : `map`

`map f [a, b, c] = [f a, f b, f c]`. C'est le `map` de tous les langages fonctionnels.

## À prouver
1. `map_concat : map f (l₁ ++ l₂) = map f l₁ ++ map f l₂`
2. `map_map : map g (map f l) = map (g ∘ f) l`
3. `longueur_map : longueur (map f l) = longueur l`
4. `map_miroir : map f (miroir l) = miroir (map f l)`
-/

namespace Parcours.Listes.Liste

variable {α β γ : Type}

theorem map_concat (f : α → β) (l₁ l₂ : Liste α) : map f (l₁ ++ l₂) = map f l₁ ++ map f l₂ := by -- @exo
  induction l₁ with
  | nil => rfl
  | cons x l ih => rw [cons_concat, map_cons, map_cons, ih, cons_concat]

theorem map_map (f : α → β) (g : β → γ) (l : Liste α) : map g (map f l) = map (g ∘ f) l := by -- @exo
  induction l with
  | nil => rfl
  | cons x l ih => rw [map_cons, map_cons, map_cons, ih]; rfl

theorem longueur_map (f : α → β) (l : Liste α) : longueur (map f l) = longueur l := by -- @exo
  induction l with
  | nil => rfl
  | cons x l ih => rw [map_cons, longueur_cons, longueur_cons, ih]

theorem map_miroir (f : α → β) (l : Liste α) : map f (miroir l) = miroir (map f l) := by -- @exo
  induction l with
  | nil => rfl
  | cons x l ih => rw [map_cons, miroir_cons, miroir_cons, map_concat, ih]; rfl

end Parcours.Listes.Liste

#verifier
