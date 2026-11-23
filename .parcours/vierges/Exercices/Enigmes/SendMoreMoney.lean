import Exercices.Recurrence.Definitions
import Exercices.Listes.Pont

/-!
# SEND + MORE = MONEY

Le cryptarithme le plus célèbre (Henry Dudeney, 1924) : chaque lettre est un chiffre différent,
et `SEND + MORE = MONEY`. Trouve la solution (unique) et fais-la vérifier par Lean.

## À prouver
`send_more_money : ∃ s e n d m o r y, (tous différents) ∧ (chiffres) ∧ s ≠ 0 ∧ m ≠ 0 ∧ SEND + MORE = MONEY`

---
*Exercice* `Enigmes.SendMoreMoney` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Enigmes.SendMoreMoney` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Enigmes

/-- La valeur d'un nombre écrit avec la liste de ses chiffres. -/
def nombre (l : List Nat) : Nat := l.foldl (fun acc c => 10 * acc + c) 0

theorem send_more_money : ∃ s e n d m o r y : Nat,
    [s, e, n, d, m, o, r, y].Nodup ∧ (∀ x ∈ [s, e, n, d, m, o, r, y], x < 10) ∧ s ≠ 0 ∧ m ≠ 0 ∧
    nombre [s, e, n, d] + nombre [m, o, r, e] = nombre [m, o, n, e, y] := by
  sorry

end Parcours.Enigmes

#verifier
