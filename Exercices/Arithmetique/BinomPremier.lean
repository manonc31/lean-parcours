import Exercices.Arithmetique.LemmeEuclide
import Exercices.Combinatoire.BinomFact

/-!
# p divise les coefficients C(p, k)

Pour `p` premier et `0 < k < p`, `p` divise `C(p, k)`. Regarde la ligne 7 du triangle :
`1 7 21 35 35 21 7 1` — tous divisibles par 7, sauf les bords !

Cet exercice relie deux branches : l'arithmétique (lemme d'Euclide) et la combinatoire (factorielles).

## À prouver
1. `premier_ne_divise_fact : Premier p → n < p → ¬p ∣ fact n`
2. `premier_divise_binom : Premier p → 0 < k → k < p → p ∣ binom p k`

---
*Exercice* `Arithmetique.BinomPremier` · difficulté ★★★★☆

💡 Indices : `./parcours indice Arithmetique.BinomPremier` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Arith

open Parcours.Combi

theorem premier_ne_divise_fact {p n : Nat} (hp : Premier p) (h : n < p) : ¬p ∣ fact n := by
  sorry

theorem premier_divise_binom {p k : Nat} (hp : Premier p) (h0 : 0 < k) (hk : k < p) :
    p ∣ binom p k := by
  sorry

end Parcours.Arith

#verifier
