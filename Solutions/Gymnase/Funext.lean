/- @parcours
titre: Deux fonctions égales
difficulte: 2
requiert: Logique.Egalite
indice: `funext x` puis `exact h x`.
indice: Pour la composée, après `funext x`, c'est vrai par calcul (`rfl`).
-/
import ParcoursOutils

/-!
# Deux fonctions égales

Deux fonctions sont égales si elles donnent le même résultat partout : `funext x` transforme le but `f = g` en `f x = g x`.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem funext_exemple (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := by -- @exo
  funext x
  exact h x

theorem composee : (fun x : Nat => x + 1) ∘ (fun x => 2 * x) = fun x => 2 * x + 1 := by -- @exo
  funext x
  rfl

end Parcours.Gymnase

#verifier
