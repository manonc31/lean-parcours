import Exercices.Recurrence.ProprietesSommes
import Exercices.Listes.Pont

/-!
# Coefficients binomiaux (cours)

`binom n k` (« k parmi n », noté aussi `C(n, k)` ou `(n k)`) est le nombre de façons de choisir
`k` objets parmi `n`. On le **définit** par le triangle de Pascal :
- `binom n 0 = 1`
- `binom 0 (k + 1) = 0`
- `binom (n + 1) (k + 1) = binom n k + binom n (k + 1)`

```
n=0 :        1
n=1 :       1 1
n=2 :      1 2 1
n=3 :     1 3 3 1
n=4 :    1 4 6 4 1
```

On réutilise `somme`, `fact` et leurs propriétés (branche Récurrence).

## Ressources
- [Triangle de Pascal (Wikipédia)](https://fr.wikipedia.org/wiki/Triangle_de_Pascal)
- [Coefficient binomial (Wikipédia)](https://fr.wikipedia.org/wiki/Coefficient_binomial)

---
*Exercice* `Combinatoire.Definitions` · difficulté ★☆☆☆☆
-/

namespace Parcours.Combi

export Parcours.Recurrence (somme somme_succ somme_zero fact fact_succ fact_zero
  somme_add somme_mul somme_decale somme_congr divise_somme)

def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

theorem binom_zero_droite (n : Nat) : binom n 0 = 1 := by cases n <;> rfl
theorem binom_zero_succ (k : Nat) : binom 0 (k + 1) = 0 := rfl
theorem binom_succ_succ (n k : Nat) : binom (n + 1) (k + 1) = binom n k + binom n (k + 1) := rfl

end Parcours.Combi
