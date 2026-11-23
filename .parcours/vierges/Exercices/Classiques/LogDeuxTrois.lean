import Exercices.Recurrence.Definitions
import Exercices.Listes.Pont

/-!
# log₂ 3 est irrationnel

## Se le représenter
Si `log₂ 3 = p/q`, alors `2^p = 3^q`. Impossible : à gauche un nombre pair (si `p ≥ 1`), à droite
un nombre impair. (C'est aussi pourquoi aucune gamme musicale ne tombe juste : 12 quintes
`(3/2)¹²` ne font jamais exactement 7 octaves `2⁷`.)

## À prouver
1. `trois_pow_impair : 3 ^ b % 2 = 1`
2. `log_deux_trois : 0 < q → 2 ^ p ≠ 3 ^ q`

## Ressources
- [Comma pythagoricien (Wikipédia)](https://fr.wikipedia.org/wiki/Comma_pythagoricien)

---
*Exercice* `Classiques.LogDeuxTrois` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Classiques.LogDeuxTrois` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

theorem trois_pow_impair (b : Nat) : 3 ^ b % 2 = 1 := by
  sorry

theorem log_deux_trois (p q : Nat) (hq : 0 < q) : 2 ^ p ≠ 3 ^ q := by
  sorry

end Parcours.Classiques

#verifier
