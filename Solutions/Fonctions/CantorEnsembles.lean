/- @parcours
titre: Cantor, version ensembles
difficulte: 2
requiert: Fonctions.Inverses
indice: Ton théorème `Parcours.Logique.cantor` est importé : `Ens α` est par définition `α → Prop`.
indice: `intro hs`, puis `apply Parcours.Logique.cantor f`, et il reste à transformer `hs : Surjective f` en `∀ g, ∃ a, f a = g` (c'est la même chose !).
-/
import Solutions.Fonctions.Definitions
import Solutions.Logique.Cantor

/-!
# Cantor, version ensembles

Tu as prouvé le théorème de Cantor dans la branche Logique. Ce fichier **l'importe** :
réutilise-le pour montrer qu'aucune fonction `α → Ens α` n'est surjective.

## À prouver
`cantor_ens (f : α → Ens α) : ¬Surjective f`
-/

namespace Parcours.Fonctions

theorem cantor_ens {α : Type} (f : α → Ens α) : ¬Surjective f := by -- @exo
  intro hs
  exact Parcours.Logique.cantor f (fun g => hs g)

end Parcours.Fonctions

#verifier
