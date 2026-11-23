import Exercices.Combinatoire.BinomBase

/-!
# La formule des factorielles

`C(n, k) = n! / (k! (n-k)!)`. Sans division : `C(n, k) · k! · (n-k)! = n!`.

## À prouver
`binom_mul_fact : k ≤ n → binom n k * fact k * fact (n - k) = fact n`

---
*Exercice* `Combinatoire.BinomFact` · difficulté ★★★★☆

💡 Indices : `./parcours indice Combinatoire.BinomFact` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Combi

theorem binom_mul_fact {n k : Nat} (h : k ≤ n) : binom n k * fact k * fact (n - k) = fact n := by
  sorry

end Parcours.Combi

#verifier
