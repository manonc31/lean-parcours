import Exercices.Informatique.Expressions

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

---
*Exercice* `Informatique.Compilateur` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Informatique.Compilateur` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
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
    exec env (p ++ q) s = exec env q (exec env p s) := by
  sorry

theorem compiler_correct (env : Nat → Nat) (e : Expr) (s : List Nat) :
    exec env (compiler e) s = eval env e :: s := by
  sorry

end Parcours.Info

#verifier
