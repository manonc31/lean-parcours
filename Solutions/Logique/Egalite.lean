/- @parcours
titre: L'égalité
difficulte: 1
requiert: Logique.Implication
indice: `rw [h]` puis l'égalité devient évidente (`rw` termine par `rfl` tout seul).
indice: Pour `egal_congr`, après `rw [h]`, le but est `f b = f b`.
-/
import ParcoursOutils

/-!
# L'égalité

En Lean, l'égalité `a = b` a une seule règle de construction : `rfl : a = a`. Tout le reste
découle de la possibilité de **remplacer** `a` par `b` (`rw`). Prouve les propriétés fondamentales
de l'égalité, sans utiliser `Eq.symm` & co. (c'est toi qui les recodes !).

## À prouver
1. `egal_symm` : si `a = b` alors `b = a`.
2. `egal_trans` : si `a = b` et `b = c` alors `a = c`.
3. `egal_congr` : si `a = b` alors `f a = f b`.
4. `egal_fonctions` : si `f = g` alors `f x = g x`.

## Ressources
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/), chapitre *Quantifiers and Equality*.
-/

namespace Parcours.Logique

variable {α β : Type}

theorem egal_symm {a b : α} (h : a = b) : b = a := by -- @exo
  rw [h]

theorem egal_trans {a b c : α} (h1 : a = b) (h2 : b = c) : a = c := by -- @exo
  rw [h1, h2]

theorem egal_congr (f : α → β) {a b : α} (h : a = b) : f a = f b := by -- @exo
  rw [h]

theorem egal_fonctions {f g : α → β} (h : f = g) (x : α) : f x = g x := by -- @exo
  rw [h]

end Parcours.Logique

#verifier
