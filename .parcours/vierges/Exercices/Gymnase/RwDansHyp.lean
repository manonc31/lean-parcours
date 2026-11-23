import ParcoursOutils

/-!
# Réécrire dans une hypothèse

`rw [h1] at h2` réécrit **dans l'hypothèse** `h2` au lieu du but. Puis `exact h2`.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.RwDansHyp` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Gymnase.RwDansHyp` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem rw_dans_hyp (a b : Nat) (h1 : a = b) (h2 : a + 1 = 7) : b + 1 = 7 := by
  sorry

end Parcours.Gymnase

#verifier
