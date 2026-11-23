/- @parcours
titre: Déstructurer avec rfl
difficulte: 2
requiert: Gymnase.Subst
indice: `obtain ⟨k, rfl⟩ := h`, puis `exact ⟨k, by omega⟩`.
-/
import Solutions.Naturels.Transfert

/-!
# Déstructurer avec rfl

Dans `obtain ⟨k, rfl⟩ := h` (avec `h : ∃ k, n = 2 * k`), le motif `rfl` remplace directement `n` par `2 * k`.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem pair_plus_pair (n : Nat) (h : ∃ k, n = 2 * k) : ∃ m, n + n = 4 * m := by -- @exo
  obtain ⟨k, rfl⟩ := h
  exact ⟨k, by omega⟩

end Parcours.Gymnase

#verifier
