import Exercices.Naturels.Transfert

/-!
# Déstructurer avec rfl

Dans `obtain ⟨k, rfl⟩ := h` (avec `h : ∃ k, n = 2 * k`), le motif `rfl` remplace directement `n` par `2 * k`.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.ObtainRfl` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Gymnase.ObtainRfl` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem pair_plus_pair (n : Nat) (h : ∃ k, n = 2 * k) : ∃ m, n + n = 4 * m := by
  sorry

end Parcours.Gymnase

#verifier
