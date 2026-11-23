import ParcoursOutils

/-!
# Appliquer une fonction aux deux côtés

Si `a = b`, alors `f a = f b` : c'est `congrArg f h`. Ici la fonction est `fun x => x * 2`.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.Congr` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Gymnase.Congr` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem congr_exemple (a b : Nat) (h : a = b) : a * 2 = b * 2 := by
  sorry

end Parcours.Gymnase

#verifier
