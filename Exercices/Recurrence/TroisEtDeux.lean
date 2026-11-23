import Exercices.Recurrence.Definitions

/-!
# Trois puissance n

`3ⁿ ≥ 2ⁿ + n` pour tout `n`.

## À prouver
`trois_puissance (n : Nat) : 2 ^ n + n ≤ 3 ^ n`

---
*Exercice* `Recurrence.TroisEtDeux` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Recurrence.TroisEtDeux` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Recurrence

theorem trois_puissance (n : Nat) : 2 ^ n + n ≤ 3 ^ n := by
  sorry

end Parcours.Recurrence

#verifier
