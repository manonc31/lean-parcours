/- @parcours
titre: SEND + MORE = MONEY
difficulte: 2
requiert: Enigmes.Chevaliers
indice: `M` est forcément 1 (une retenue), donc `S` vaut 8 ou 9…
indice: La solution : `9567 + 1085 = 10652`. Donne-la avec `exact ⟨9, 5, 6, 7, 1, 0, 8, 2, by decide⟩`.
-/
import Solutions.Recurrence.Definitions
import Solutions.Listes.Pont

/-!
# SEND + MORE = MONEY

Le cryptarithme le plus célèbre (Henry Dudeney, 1924) : chaque lettre est un chiffre différent,
et `SEND + MORE = MONEY`. Trouve la solution (unique) et fais-la vérifier par Lean.

## À prouver
`send_more_money : ∃ s e n d m o r y, (tous différents) ∧ (chiffres) ∧ s ≠ 0 ∧ m ≠ 0 ∧ SEND + MORE = MONEY`
-/

namespace Parcours.Enigmes

/-- La valeur d'un nombre écrit avec la liste de ses chiffres. -/
def nombre (l : List Nat) : Nat := l.foldl (fun acc c => 10 * acc + c) 0

theorem send_more_money : ∃ s e n d m o r y : Nat,
    [s, e, n, d, m, o, r, y].Nodup ∧ (∀ x ∈ [s, e, n, d, m, o, r, y], x < 10) ∧ s ≠ 0 ∧ m ≠ 0 ∧
    nombre [s, e, n, d] + nombre [m, o, r, e] = nombre [m, o, n, e, y] := by -- @exo
  exact ⟨9, 5, 6, 7, 1, 0, 8, 2, by decide⟩

end Parcours.Enigmes

#verifier
