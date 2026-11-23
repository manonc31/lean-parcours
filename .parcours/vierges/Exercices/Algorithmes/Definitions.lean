import Exercices.Tris.Definitions
import Exercices.Recurrence.Definitions

/-!
# Prouver des programmes (cours)

Dans cette branche, chaque exercice est un **programme** (déjà écrit, ou à écrire) accompagné de
sa **spécification**. Le programme est souvent plus rapide ou plus malin que la définition naïve ;
la preuve garantit qu'il calcule bien la même chose, pour **toutes** les entrées (pas seulement
celles qu'on aurait testées).

## Outils
- `fun_induction f x with …` : récurrence qui suit les appels récursifs de `f`.
- `split` : sépare les cas d'un `if … then … else …` ou d'un `match` dans le but.
- `simp only [f]` / `rw [f]` : déplie la définition de `f`.
- Tous les lemmes de `Nat` et `List` sont permis (les Ponts sont franchis), ainsi que `omega` et `grind`.

## Ressources
- [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/)
- [Software Foundations, volume 3 (Verified Functional Algorithms)](https://softwarefoundations.cis.upenn.edu/vfa-current/index.html)

---
*Exercice* `Algorithmes.Definitions` · difficulté ★☆☆☆☆
-/
