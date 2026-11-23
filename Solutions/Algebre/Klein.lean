/- @parcours
titre: Le groupe de Klein
difficulte: 1
requiert: Algebre.Triangle
indice: Tout se calcule : `decide`.
-/
import Solutions.Listes.Pont
import Solutions.Recurrence.Definitions

/-!
# Le groupe de Klein

Le groupe de Klein a 4 éléments : `(false, false)` (le neutre), et trois autres, chacun étant son
propre inverse. On le réalise avec des couples de booléens et le OU exclusif composante par
composante : c'est le groupe des symétries d'un rectangle (identité, deux réflexions, demi-tour).
Contrairement au groupe des rotations d'un carré, il n'est pas **cyclique** : aucun élément ne
l'engendre à lui seul.

## À prouver
1. `commutatif`, `involutif` : tout élément est son propre inverse.
2. `pas_cyclique` : les puissances de chaque élément ne donnent jamais les 4 éléments.

## Ressources
- [Groupe de Klein (Wikipédia)](https://fr.wikipedia.org/wiki/Groupe_de_Klein)
-/

namespace Parcours.Algebre

abbrev V4 := Bool × Bool

def op (x y : V4) : V4 := (x.1 ^^ y.1, x.2 ^^ y.2)

def elements : List V4 := [(false, false), (false, true), (true, false), (true, true)]

theorem commutatif : ∀ x ∈ elements, ∀ y ∈ elements, op x y = op y x := by -- @exo
  decide

theorem involutif : ∀ x ∈ elements, op x x = (false, false) := by -- @exo
  decide

theorem pas_cyclique : ∀ x ∈ elements, [x, op x x, op x (op x x), op x (op x (op x x))].eraseDups.length < 4 := by -- @exo
  decide

end Parcours.Algebre

#verifier
