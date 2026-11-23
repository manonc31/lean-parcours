import ParcoursOutils

/-!
# Lean sait calculer

Quand les deux côtés d'une égalité se **calculent** en la même valeur, `rfl` suffit : Lean évalue `2 + 3` tout seul. (On peut aussi demander à Lean de calculer avec `#eval 2 + 3` : essaie !)

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.Calcul` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Gymnase.Calcul` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem calcul : (2 : Nat) + 3 = 5 := by
  sorry

theorem calcul_bis : (7 : Nat) * 6 = 42 := by
  sorry

end Parcours.Gymnase

#verifier
