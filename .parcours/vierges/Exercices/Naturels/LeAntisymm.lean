import Exercices.Naturels.LeBase
import Exercices.Naturels.AddSelf

/-!
# Antisymétrie

Si `a ≤ b` et `b ≤ a`, alors `a = b`. Avec la réflexivité et la transitivité, ça fait de `≤`
une **relation d'ordre**.

## À prouver
`le_antisymm (a b : ℕ) : a ≤ b → b ≤ a → a = b`

---
*Exercice* `Naturels.LeAntisymm` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Naturels.LeAntisymm` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

theorem le_antisymm (a b : ℕ) (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  sorry

end Parcours.ℕ

#verifier
