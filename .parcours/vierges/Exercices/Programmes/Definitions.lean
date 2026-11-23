import Exercices.Algorithmes.Definitions

/-!
# Programmes ludiques (cours)

Dans cette branche, on écrit (ou on lit) de **petits programmes amusants** — FizzBuzz, le chiffre
de César, la multiplication russe, les huit reines, le mélange parfait d'un magicien… — puis on
**prouve** qu'ils font ce qu'on croit.

## Deux façons de convaincre Lean
1. **Calculer** : quand l'énoncé porte sur des valeurs précises (« il y a 92 solutions au problème
   des huit reines »), Lean peut faire le calcul lui-même : `decide`. Pour les gros calculs,
   `decide +kernel` fait faire le calcul directement par le noyau de Lean (plus rapide).
2. **Raisonner** : pour un énoncé sur **toutes** les entrées (« César puis César inverse redonne
   le message »), il faut une vraie preuve, souvent par récurrence.

## Outils
- `fun_induction f x` : récurrence qui suit les appels récursifs de `f`, et déplie `f x` dans le
  but. Il y a un cas par branche de la définition.
- `termination_by` / `decreasing_by` : quand une fonction ne s'appelle pas sur un argument
  structurellement plus petit (par exemple `n / 2`), on dit à Lean ce qui décroît.
- `split` : sépare les cas d'un `if … then … else …`.
- Tous les lemmes de `Nat` et `List` sont permis, ainsi que `omega` et `grind`.

## Une fonction utile
`repeter f n x` applique `n` fois la fonction `f` à `x`.

## Ressources
- [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/)
- [Rosetta Code](https://rosettacode.org/) : les mêmes petits programmes dans des centaines de langages.

---
*Exercice* `Programmes.Definitions` · difficulté ★☆☆☆☆
-/

namespace Parcours.Prog

/-- `repeter f n x = f (f (… (f x)))` (`n` fois). -/
def repeter {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => repeter f n (f x)

end Parcours.Prog
