import Exercices.Algorithmes.Definitions

/-!
# La méthode de Horner

Pour évaluer un polynôme `c₀ + c₁x + c₂x² + ⋯ + cₙxⁿ`, la méthode naïve calcule toutes les puissances.
Horner (1819, mais connue en Chine au XIIIᵉ siècle) réécrit : `c₀ + x(c₁ + x(c₂ + ⋯))`.
Seulement `n` multiplications, et c'est optimal !

Un polynôme est la liste de ses coefficients `[c₀, c₁, …, cₙ]`.

## À prouver
1. `evalAux_eq : evalAux p x i = x ^ i * horner p x`
2. `horner_correct : horner p x = evalNaif p x`

## Ressources
- [Méthode de Ruffini-Horner (Wikipédia)](https://fr.wikipedia.org/wiki/M%C3%A9thode_de_Ruffini-Horner)

---
*Exercice* `Algorithmes.Horner` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Algorithmes.Horner` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Algo

/-- `evalAux p x i = c₀ xⁱ + c₁ xⁱ⁺¹ + ⋯` -/
def evalAux : List Nat → Nat → Nat → Nat
  | [], _, _ => 0
  | c :: p, x, i => c * x ^ i + evalAux p x (i + 1)

def evalNaif (p : List Nat) (x : Nat) : Nat := evalAux p x 0

def horner : List Nat → Nat → Nat
  | [], _ => 0
  | c :: p, x => c + x * horner p x

theorem evalAux_eq (p : List Nat) (x i : Nat) : evalAux p x i = x ^ i * horner p x := by
  sorry

theorem horner_correct (p : List Nat) (x : Nat) : horner p x = evalNaif p x := by
  sorry

end Parcours.Algo

#verifier
