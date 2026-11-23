import Exercices.Listes.Pont

/-!
# La tactique simp

`simp` applique automatiquement des centaines de lemmes de simplification (`x + 0 = x`, `l ++ [] = l`, `(l₁ ++ l₂).length = …`…). Depuis les Ponts, ces lemmes sont débloqués. `simp [h]` ajoute une hypothèse `h` aux règles utilisées.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.Simp` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Gymnase.Simp` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem simp1 (l : List Nat) : (l ++ []).length = l.length := by
  sorry

theorem simp2 (l₁ l₂ : List Nat) (h : l₁.length = 3) : (l₁ ++ l₂).length = 3 + l₂.length := by
  sorry

end Parcours.Gymnase

#verifier
