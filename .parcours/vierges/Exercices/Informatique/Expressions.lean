import Exercices.Listes.Pont
import Exercices.Logique.Bilan

/-!
# Un simplificateur d'expressions prouvé

Une expression arithmétique est un **arbre** : constantes, variables `x₀, x₁, …`, sommes, produits.
`eval env e` calcule sa valeur (où `env i` est la valeur de la variable `xᵢ`).

Un compilateur simplifie les expressions : `e + 0 ↦ e`, `1 × e ↦ e`… Une erreur dans ce genre
d'optimisation, et le programme compilé calcule autre chose que le programme écrit ! Prouve que la
simplification **préserve toujours la valeur**.

## À prouver
1. `eval_mkAdd : eval env (mkAdd e₁ e₂) = eval env e₁ + eval env e₂`
2. `eval_mkMul : eval env (mkMul e₁ e₂) = eval env e₁ * eval env e₂`
3. `eval_simplifier : eval env (simplifier e) = eval env e`

## Ressources
- [Arbre syntaxique (Wikipédia)](https://fr.wikipedia.org/wiki/Arbre_syntaxique)

---
*Exercice* `Informatique.Expressions` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Informatique.Expressions` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Info

inductive Expr where
  | cst (n : Nat)
  | var (i : Nat)
  | add (e₁ e₂ : Expr)
  | mul (e₁ e₂ : Expr)
  deriving Repr

open Expr

def eval (env : Nat → Nat) : Expr → Nat
  | cst n => n
  | var i => env i
  | add e₁ e₂ => eval env e₁ + eval env e₂
  | mul e₁ e₂ => eval env e₁ * eval env e₂

/-- Une somme « intelligente » qui supprime les `+ 0`. -/
def mkAdd : Expr → Expr → Expr
  | cst 0, e => e
  | e, cst 0 => e
  | e₁, e₂ => add e₁ e₂

/-- Un produit « intelligent » qui supprime les `× 1`. -/
def mkMul : Expr → Expr → Expr
  | cst 1, e => e
  | e, cst 1 => e
  | e₁, e₂ => mul e₁ e₂

def simplifier : Expr → Expr
  | add e₁ e₂ => mkAdd (simplifier e₁) (simplifier e₂)
  | mul e₁ e₂ => mkMul (simplifier e₁) (simplifier e₂)
  | e => e

theorem eval_mkAdd (env : Nat → Nat) (e₁ e₂ : Expr) :
    eval env (mkAdd e₁ e₂) = eval env e₁ + eval env e₂ := by
  sorry

theorem eval_mkMul (env : Nat → Nat) (e₁ e₂ : Expr) :
    eval env (mkMul e₁ e₂) = eval env e₁ * eval env e₂ := by
  sorry

theorem eval_simplifier (env : Nat → Nat) (e : Expr) : eval env (simplifier e) = eval env e := by
  sorry

end Parcours.Info

#verifier
