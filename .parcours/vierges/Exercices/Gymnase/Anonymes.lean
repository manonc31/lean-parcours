import ParcoursOutils

/-!
# Les fonctions anonymes

`fun x => x + 1` est la fonction qui à `x` associe `x + 1` (on peut aussi écrire `(· + 1)`). L'appliquer, c'est **remplacer** `x` : Lean le fait par calcul.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.Anonymes` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Gymnase.Anonymes` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem anonyme : (fun x : Nat => x + 1) 2 = 3 := by
  sorry

theorem eta (f : Nat → Nat) : (fun x => f x) = f := by
  sorry

end Parcours.Gymnase

#verifier
