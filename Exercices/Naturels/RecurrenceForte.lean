import Exercices.Naturels.Strict

/-!
# La récurrence forte

La récurrence ordinaire : pour prouver `P (n+1)`, on suppose `P n`.
La récurrence **forte** : pour prouver `P n`, on suppose `P m` pour **tous** les `m < n`.

C'est plus puissant en apparence, mais on peut la **déduire** de la récurrence ordinaire !
Elle servira partout : décomposition en facteurs premiers, algorithmes « diviser pour régner »…

## À prouver
`recurrence_forte (P : ℕ → Prop) (h : ∀ n, (∀ m, m < n → P m) → P n) (n : ℕ) : P n`

## Ressources
- [Récurrence forte (Wikipédia)](https://fr.wikipedia.org/wiki/Raisonnement_par_r%C3%A9currence#R%C3%A9currence_forte)

---
*Exercice* `Naturels.RecurrenceForte` · difficulté ★★★★☆

💡 Indices : `./parcours indice Naturels.RecurrenceForte` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

theorem recurrence_forte (P : ℕ → Prop) (h : ∀ n, (∀ m, m < n → P m) → P n) (n : ℕ) : P n := by
  sorry

end Parcours.ℕ

#verifier
