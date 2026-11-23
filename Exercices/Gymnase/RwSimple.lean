import ParcoursOutils

/-!
# Remplacer une variable

`rw [h]` remplace `x` par `3` partout dans le but. Ensuite, `rw` essaie `rfl` tout seul.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.RwSimple` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Gymnase.RwSimple` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem rw_simple (x : Nat) (h : x = 3) : x + x = 6 := by
  sorry

end Parcours.Gymnase

#verifier
