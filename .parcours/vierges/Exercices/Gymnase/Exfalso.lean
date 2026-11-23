import ParcoursOutils

/-!
# Du faux, on déduit n'importe quoi

Si tu as `h : False`, `exfalso` remplace le but par `False`, puis `exact h`. (Ou directement `exact h.elim`.)

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.Exfalso` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Gymnase.Exfalso` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem exfalso_exemple (h : False) : (2 : Nat) + 2 = 5 := by
  sorry

end Parcours.Gymnase

#verifier
