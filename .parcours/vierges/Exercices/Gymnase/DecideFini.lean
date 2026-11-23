import ParcoursOutils

/-!
# Décider sur un ensemble fini

`Fin n` est le type des entiers `< n`. Un énoncé `∀ x : Fin 4, …` n'a que 4 cas : `decide` les vérifie tous.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.DecideFini` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Gymnase.DecideFini` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem fini1 : ∀ x : Fin 4, x.val * x.val < 10 := by
  sorry

theorem fini2 : (List.range 5).foldl (· + ·) 0 = 10 := by
  sorry

end Parcours.Gymnase

#verifier
