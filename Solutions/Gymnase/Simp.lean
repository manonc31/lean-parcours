/- @parcours
titre: La tactique simp
difficulte: 2
requiert: Listes.Pont
indice: `simp`.
indice: `simp [h]`.
-/
import Solutions.Listes.Pont

/-!
# La tactique simp

`simp` applique automatiquement des centaines de lemmes de simplification (`x + 0 = x`, `l ++ [] = l`, `(l₁ ++ l₂).length = …`…). Depuis les Ponts, ces lemmes sont débloqués. `simp [h]` ajoute une hypothèse `h` aux règles utilisées.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem simp1 (l : List Nat) : (l ++ []).length = l.length := by -- @exo
  simp

theorem simp2 (l₁ l₂ : List Nat) (h : l₁.length = 3) : (l₁ ++ l₂).length = 3 + l₂.length := by -- @exo
  simp [h]

end Parcours.Gymnase

#verifier
