import ParcoursOutils

/-!
# Raisonner sur les booléens

Un booléen est `true` ou `false`. `cases b` examine les deux cas ; dans chacun, `rfl` calcule. Raccourci : `cases b <;> rfl` applique `rfl` à tous les cas.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.Booleens` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Gymnase.Booleens` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem et_vrai (b : Bool) : (b && true) = b := by
  sorry

theorem non_non (b : Bool) : (!(!b)) = b := by
  sorry

theorem ou_comm_bool (a b : Bool) : (a || b) = (b || a) := by
  sorry

end Parcours.Gymnase

#verifier
