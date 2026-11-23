/- @parcours
titre: La méthode de Horner
difficulte: 3
indice: Généralise : `evalAux p x i = x ^ i * horner p x`, par récurrence sur `p` en généralisant `i`.
indice: Cas `c :: p` : `evalAux (c :: p) x i = c * x ^ i + evalAux p x (i + 1)`, puis `ih (i + 1)`, `Nat.pow_succ`, et `grind`.
-/
import Solutions.Algorithmes.Definitions

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

theorem evalAux_eq (p : List Nat) (x i : Nat) : evalAux p x i = x ^ i * horner p x := by -- @exo
  induction p generalizing i with
  | nil => simp [evalAux, horner]
  | cons c p ih =>
    simp only [evalAux, horner, ih (i + 1), Nat.pow_succ]
    grind

theorem horner_correct (p : List Nat) (x : Nat) : horner p x = evalNaif p x := by -- @exo
  rw [evalNaif, evalAux_eq, Nat.pow_zero, Nat.one_mul]

end Parcours.Algo

#verifier
