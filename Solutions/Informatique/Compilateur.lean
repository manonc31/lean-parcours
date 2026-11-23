/- @parcours
titre: Un compilateur prouvé correct
difficulte: 3
indice: `exec_append` : récurrence sur `p` en généralisant `s`. Dans le cas `i :: p`, fais `cases i` et, pour `add`/`mul`, regarde la forme de la pile (`rcases s with _ | ⟨b, _ | ⟨a, s⟩⟩`).
indice: Plus simple : `fun_induction exec env p s` puis `simp_all [exec]` dans chaque cas.
indice: `compiler_correct` : récurrence sur `e` en généralisant `s`. Pour `add e₁ e₂` : `simp only [compiler, exec_append, ih₁, ih₂]` puis `rfl`.
-/
import Solutions.Informatique.Expressions

/-!
# Un compilateur prouvé correct

On compile les expressions vers une **machine à pile** (comme la JVM ou les calculatrices HP) :
- `push n` empile `n`, `load i` empile la valeur de la variable `xᵢ` ;
- `add` (resp. `mul`) dépile deux nombres et empile leur somme (resp. produit).

Exemple : `(x₀ + 2) × 3` se compile en `load 0, push 2, add, push 3, mul`.

Le théorème de correction : exécuter le code compilé **empile exactement la valeur** de l'expression.
C'est le cœur de CompCert, un vrai compilateur C prouvé correct (en Coq) et utilisé dans l'aviation.

## À prouver
1. `exec_append : exec env (p ++ q) s = exec env q (exec env p s)`
2. `compiler_correct : exec env (compiler e) s = eval env e :: s`

## Ressources
- [Machine à pile (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Stack_machine)
- [CompCert](https://compcert.org/)
-/

namespace Parcours.Info

inductive Instr where
  | push (n : Nat)
  | load (i : Nat)
  | add
  | mul

open Instr

def exec (env : Nat → Nat) : List Instr → List Nat → List Nat
  | [], s => s
  | push n :: p, s => exec env p (n :: s)
  | load i :: p, s => exec env p (env i :: s)
  | add :: p, b :: a :: s => exec env p ((a + b) :: s)
  | mul :: p, b :: a :: s => exec env p ((a * b) :: s)
  | _ :: p, s => exec env p s

def compiler : Expr → List Instr
  | .cst n => [push n]
  | .var i => [load i]
  | .add e₁ e₂ => compiler e₁ ++ compiler e₂ ++ [add]
  | .mul e₁ e₂ => compiler e₁ ++ compiler e₂ ++ [mul]

theorem exec_append (env : Nat → Nat) (p q : List Instr) (s : List Nat) :
    exec env (p ++ q) s = exec env q (exec env p s) := by -- @exo
  fun_induction exec env p s <;> simp_all [exec]

theorem compiler_correct (env : Nat → Nat) (e : Expr) (s : List Nat) :
    exec env (compiler e) s = eval env e :: s := by -- @exo
  induction e generalizing s with
  | cst n => rfl
  | var i => rfl
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [compiler, exec_append, ih₁, ih₂]
    rfl
  | mul e₁ e₂ ih₁ ih₂ =>
    simp only [compiler, exec_append, ih₁, ih₂]
    rfl

end Parcours.Info

#verifier
