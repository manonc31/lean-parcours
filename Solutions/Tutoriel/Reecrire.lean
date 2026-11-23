/- @parcours
titre: Réécrire avec rw
difficulte: 1
indice: `rw [h1]` remplace `a` par `b` dans le but. Que devient le but ensuite ?
indice: `rw [h1, h2]` fait les deux réécritures à la suite ; `rw` essaie ensuite `rfl` tout seul.
-/
import Solutions.Tutoriel.Bienvenue

/-!
# Réécrire avec `rw`

Si tu as une hypothèse `h : a = b`, la tactique **`rw [h]`** remplace tous les `a` du but par des `b`.
Après une réécriture, `rw` essaie automatiquement `rfl` : si le but devient `c = c`, il disparaît.

- `rw [h]` : réécrit de gauche à droite (les `a` deviennent des `b`).
- `rw [← h]` : réécrit de droite à gauche (les `b` deviennent des `a`). Le `←` se tape `\l` puis espace.
- `rw [h1, h2]` : plusieurs réécritures à la suite.
- `rw [h] at h3` : réécrit dans l'hypothèse `h3` au lieu du but.

## À prouver
1. `reecrire` : si `a = b` et `b = c`, alors `a = c`.
2. `reecrire_envers` : si `a = b` et `a + c = 10`, alors `b + c = 10`.

## Ressources
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/), chapitre *Tactics* (section *Rewriting*).
-/

namespace Parcours.Tutoriel

theorem reecrire (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by -- @exo
  rw [h1, h2]

theorem reecrire_envers (a b c : Nat) (h1 : a = b) (h2 : a + c = 10) : b + c = 10 := by -- @exo
  rw [← h1]
  exact h2

end Parcours.Tutoriel

#verifier
