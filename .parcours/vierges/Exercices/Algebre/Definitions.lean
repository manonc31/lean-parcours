import Exercices.Logique.Bilan
import Exercices.Naturels.Transfert

/-!
# Les groupes (cours)

Un **groupe** est un ensemble `G` muni d'une opération `*`, d'un élément `1` et d'un inverse `⁻¹`
(tapé `\inv`) tels que :
- `(a * b) * c = a * (b * c)`  (associativité, `Groupe.mul_assoc`)
- `1 * a = a`                  (neutre à gauche, `Groupe.one_mul`)
- `a⁻¹ * a = 1`                (inverse à gauche, `Groupe.inv_mul`)

C'est **tout** ! On ne suppose même pas `a * 1 = a` ni `a * a⁻¹ = 1` : tu vas les **déduire**.
On ne suppose pas non plus `a * b = b * a` (les groupes ne sont pas forcément commutatifs :
pense aux rotations d'un Rubik's cube).

Les nombres (`+`), les rotations, les permutations, les symétries d'un cristal… sont des groupes :
tout ce que tu prouves ici est vrai pour **tous** à la fois.

## Ressources
- [Groupe (Wikipédia)](https://fr.wikipedia.org/wiki/Groupe_%28math%C3%A9matiques%29)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/), chapitre *Structures*.

---
*Exercice* `Algebre.Definitions` · difficulté ★☆☆☆☆
-/

namespace Parcours.Algebre

/-- Un groupe, avec les axiomes minimaux « à gauche ». -/
class Groupe (G : Type) extends Mul G, One G, Inv G where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
  one_mul : ∀ a : G, 1 * a = a
  inv_mul : ∀ a : G, a⁻¹ * a = 1

end Parcours.Algebre
