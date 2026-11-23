import Exercices.Arithmetique.FacteurPremier

/-!
# Décomposition en facteurs premiers (existence)

Tout entier `n ≥ 1` est un produit de nombres premiers. On le représente par une liste
`l : List Nat` (les listes de Lean : `[2, 2, 3]` pour 12), avec `l.prod` le produit.

## À prouver
`decomposition (n : Nat) : 1 ≤ n → ∃ l : List Nat, (∀ p ∈ l, Premier p) ∧ l.prod = n`

## Ressources
- [Décomposition en produit de facteurs premiers (Wikipédia)](https://fr.wikipedia.org/wiki/D%C3%A9composition_en_produit_de_facteurs_premiers)

---
*Exercice* `Arithmetique.Decomposition` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Arithmetique.Decomposition` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Arith

theorem decomposition (n : Nat) (hn : 1 ≤ n) :
    ∃ l : List Nat, (∀ p ∈ l, Premier p) ∧ l.prod = n := by
  sorry

end Parcours.Arith

#verifier
