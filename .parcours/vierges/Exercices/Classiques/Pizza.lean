import Exercices.Recurrence.Definitions

/-!
# Découper une pizza

## Se le représenter
Avec `n` coupes droites (sans passer par le même point), combien de morceaux au maximum ? La `n`-ième
coupe croise les `n − 1` précédentes, et traverse donc `n` morceaux, qu'elle coupe chacun en deux :
`n` morceaux de plus. (Le « problème du traiteur paresseux ».) Formule : `(n² + n + 2)/2`.

## À prouver
`pizza (n : Nat) : 2 * morceaux n = n * n + n + 2`

## Ressources
- [Suite du traiteur paresseux (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Lazy_caterer%27s_sequence)

---
*Exercice* `Classiques.Pizza` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Classiques.Pizza` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

open Parcours.Recurrence

def morceaux : Nat → Nat
  | 0 => 1
  | n + 1 => morceaux n + (n + 1)

theorem pizza (n : Nat) : 2 * morceaux n = n * n + n + 2 := by
  sorry

end Parcours.Classiques

#verifier
