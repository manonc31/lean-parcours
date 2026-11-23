/- @parcours
titre: Pas de plus petit que zéro
difficulte: 2
requiert: Logique.NegQuantif
indice: `intro h`, puis applique `h` à `0`.
indice: Avec `hm : m < 0`, `cases hm` termine (il n'y a aucun cas possible).
-/
import ParcoursOutils

/-!
# Pas de plus petit que zéro

Contre-exemple à « pour tout `n`, il existe `m < n` » : prends `n = 0` ! En Lean, `m < 0` est
impossible, et `cases` le voit (aucune règle ne permet de construire une preuve de `m < 0`).

## À prouver
`pas_de_plus_petit : ¬∀ n : Nat, ∃ m, m < n`
-/

namespace Parcours.Logique

theorem pas_de_plus_petit : ¬∀ n : Nat, ∃ m, m < n := by -- @exo
  intro h
  obtain ⟨m, hm⟩ := h 0
  cases hm

end Parcours.Logique

#verifier
