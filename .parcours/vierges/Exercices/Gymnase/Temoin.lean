import ParcoursOutils

/-!
# Donner un témoin

Pour prouver `∃ n, n + 2 = 5`, il suffit de donner `n` : `exact ⟨3, rfl⟩` (le témoin, puis la preuve).

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.Temoin` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Gymnase.Temoin` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem temoin : ∃ n : Nat, n + 2 = 5 := by
  sorry

theorem temoin_double : ∃ a b : Nat, a + b = 10 ∧ a = 2 * b + 1 := by
  sorry

end Parcours.Gymnase

#verifier
