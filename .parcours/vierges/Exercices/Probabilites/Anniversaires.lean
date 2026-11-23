import Exercices.Probabilites.Definitions

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

---
*Exercice* `Probabilites.Anniversaires` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Probabilites.Anniversaires` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Proba

/-- Nombre de façons d'attribuer `k` anniversaires tous distincts : `365 × 364 × ⋯`. -/
def pasDeCollision : Nat → Nat
  | 0 => 1
  | k + 1 => pasDeCollision k * (365 - k)

theorem vingt_trois : 2 * pasDeCollision 23 < 365 ^ 23 := by
  sorry

theorem vingt_deux : ¬(2 * pasDeCollision 22 < 365 ^ 22) := by
  sorry

end Parcours.Proba

#verifier
