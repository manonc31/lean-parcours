/- @parcours
titre: Construire des inverses avec l'axiome du choix
difficulte: 3
indice: Surjection : pour chaque `y`, `h y : ∃ x, f x = y`. `Classical.choose (h y)` est un tel `x`, et `Classical.choose_spec (h y)` prouve `f (Classical.choose (h y)) = y`.
indice: Donc : `exact ⟨fun y => Classical.choose (h y), fun y => Classical.choose_spec (h y)⟩`.
indice: Injection : définis `g y := if hy : ∃ x, f x = y then Classical.choose hy else a0` (où `a0` vient de `Nonempty α`). Il faut `open Classical in` ou `haveI := Classical.propDecidable` pour pouvoir écrire ce `if`.
indice: Puis, pour `x` donné, `dite_eq_left ⟨x, rfl⟩` (anciennement `dif_pos`) déplie le `if`, et l'injectivité appliquée à `Classical.choose_spec` conclut.
-/
import Solutions.Fonctions.Definitions

/-!
# Construire des inverses avec l'axiome du choix

Une surjection a un inverse à droite, une injection (de domaine non vide) un inverse à gauche.
Mais pour **construire** ces inverses, il faut **choisir** un antécédent pour chaque `y` :
c'est l'axiome du choix (`Classical.choose`).

## À prouver
1. `inverse_droite (h : Surjective f) : ∃ g : β → α, ∀ y, f (g y) = y`
2. `inverse_gauche [Nonempty α] (h : Injective f) : ∃ g : β → α, ∀ x, g (f x) = x`

## Ressources
- [Axiome du choix (Wikipédia)](https://fr.wikipedia.org/wiki/Axiome_du_choix)
-/

namespace Parcours.Fonctions

variable {α β : Type} {f : α → β}

theorem inverse_droite (h : Surjective f) : ∃ g : β → α, ∀ y, f (g y) = y := by -- @exo
  exact ⟨fun y => Classical.choose (h y), fun y => Classical.choose_spec (h y)⟩

theorem inverse_gauche [Nonempty α] (h : Injective f) : ∃ g : β → α, ∀ x, g (f x) = x := by -- @exo
  haveI := Classical.propDecidable
  obtain ⟨a0⟩ := ‹Nonempty α›
  refine ⟨fun y => if hy : ∃ x, f x = y then Classical.choose hy else a0, ?_⟩
  intro x
  have hx : ∃ x', f x' = f x := ⟨x, rfl⟩
  simp only [dite_eq_left hx]
  exact h _ _ (Classical.choose_spec hx)

end Parcours.Fonctions

#verifier
