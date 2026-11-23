import Exercices.Combinatoire.BinomBase

/-!
# La somme d'une ligne du triangle

`C(n,0) + C(n,1) + ⋯ + C(n,n) = 2ⁿ` : c'est le nombre total de parties d'un ensemble à `n` éléments.

## À prouver
1. `somme_pascal : somme (binom (n + 1)) (m + 1) = somme (binom n) (m + 1) + somme (binom n) m`
2. `somme_ligne (n : Nat) : somme (binom n) (n + 1) = 2 ^ n`

---
*Exercice* `Combinatoire.SommeLigne` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Combinatoire.SommeLigne` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Combi

theorem somme_pascal (n m : Nat) :
    somme (binom (n + 1)) (m + 1) = somme (binom n) (m + 1) + somme (binom n) m := by
  sorry

theorem somme_ligne (n : Nat) : somme (binom n) (n + 1) = 2 ^ n := by
  sorry

end Parcours.Combi

#verifier
