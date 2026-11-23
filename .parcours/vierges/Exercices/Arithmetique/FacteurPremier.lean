import Exercices.Arithmetique.DiviseOrdre

/-!
# Tout nombre a un facteur premier

Tout entier `n ≥ 2` est divisible par au moins un nombre premier.

## Récurrence forte sur `Nat`
`induction n using Nat.strongRecOn with | ind n ih => …` : `ih` dit que la propriété
est vraie pour tous les `m < n`.

## À prouver
`existe_facteur_premier (n : Nat) : 2 ≤ n → ∃ p, Premier p ∧ p ∣ n`

---
*Exercice* `Arithmetique.FacteurPremier` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Arithmetique.FacteurPremier` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Arith

theorem existe_facteur_premier (n : Nat) (hn : 2 ≤ n) : ∃ p, Premier p ∧ p ∣ n := by
  sorry

end Parcours.Arith

#verifier
