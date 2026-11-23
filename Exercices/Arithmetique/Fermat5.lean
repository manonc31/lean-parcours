import Exercices.Arithmetique.Definitions

/-!
# Fermat s'est trompé

Pierre de Fermat avait conjecturé (1640) que tous les nombres `Fₙ = 2^(2ⁿ) + 1` sont premiers :
3, 5, 17, 257, 65537… En 1732, Euler trouve que `F₅ = 4 294 967 297 = 641 × 6 700 417`.
On ne connaît aujourd'hui **aucun** autre nombre de Fermat premier.

## À prouver
1. `valeurs` : `F₀` à `F₄`.
2. `euler : fermat 5 = 641 * 6700417`
3. `astuce` : pourquoi 641 ? Car `641 = 5 × 2⁷ + 1 = 5⁴ + 2⁴`.

## Ressources
- [Nombre de Fermat (Wikipédia)](https://fr.wikipedia.org/wiki/Nombre_de_Fermat)

---
*Exercice* `Arithmetique.Fermat5` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Arithmetique.Fermat5` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Arith

def fermat (n : Nat) : Nat := 2 ^ (2 ^ n) + 1

theorem valeurs : fermat 0 = 3 ∧ fermat 1 = 5 ∧ fermat 2 = 17 ∧ fermat 3 = 257 ∧ fermat 4 = 65537 := by
  sorry

theorem euler : fermat 5 = 641 * 6700417 := by
  sorry

theorem astuce : 641 = 5 * 2 ^ 7 + 1 ∧ 641 = 5 ^ 4 + 2 ^ 4 := by
  sorry

end Parcours.Arith

#verifier
