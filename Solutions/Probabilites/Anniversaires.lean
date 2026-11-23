/- @parcours
celebre: 93
titre: Le paradoxe des anniversaires
difficulte: 2
indice: `pasDeCollision k` est le nombre de façons de choisir `k` dates **toutes différentes** : `365 × 364 × ⋯ × (365 - k + 1)`. Le nombre total est `365 ^ k`.
indice: « P(deux personnes ont le même anniversaire) > 1/2 » équivaut à « P(toutes différentes) < 1/2 », soit `2 * pasDeCollision k < 365 ^ k`.
indice: `decide` sait calculer avec des nombres de 60 chiffres !
-/
import Solutions.Probabilites.Definitions

/-!
# Le paradoxe des anniversaires

Combien faut-il de personnes dans une pièce pour avoir plus d'une chance sur deux que deux
d'entre elles aient le même anniversaire ? Réponse : **23** seulement ! (Avec 365 jours équiprobables.)
Avec 70 personnes, c'est plus de 99,9 %.

Ce paradoxe est à la base des attaques « anniversaire » contre les fonctions de hachage en cryptographie.

## À prouver
1. `vingt_trois : 2 * pasDeCollision 23 < 365 ^ 23` (avec 23 personnes, la probabilité d'une collision dépasse 1/2)
2. `vingt_deux : ¬(2 * pasDeCollision 22 < 365 ^ 22)` (avec 22, non : 23 est bien le seuil)

## Ressources
- [Paradoxe des anniversaires (Wikipédia)](https://fr.wikipedia.org/wiki/Paradoxe_des_anniversaires)
-/

namespace Parcours.Proba

/-- Nombre de façons d'attribuer `k` anniversaires tous distincts : `365 × 364 × ⋯`. -/
def pasDeCollision : Nat → Nat
  | 0 => 1
  | k + 1 => pasDeCollision k * (365 - k)

theorem vingt_trois : 2 * pasDeCollision 23 < 365 ^ 23 := by -- @exo
  decide

theorem vingt_deux : ¬(2 * pasDeCollision 22 < 365 ^ 22) := by -- @exo
  decide

end Parcours.Proba

#verifier
