/- @parcours
titre: Antisymétrie
difficulte: 3
indice: `obtain ⟨c, hc⟩ := hab` et `obtain ⟨d, hd⟩ := hba` : `hc : b = a + c`, `hd : a = b + d`.
indice: En remplaçant, `a = a + c + d = a + (c + d)`. Donc `c + d = 0` (`add_right_eq_self`), donc `c = 0` (`add_eq_zero`).
indice: Pour réécrire `b` dans `hd` : `rw [hc, add_assoc] at hd`. Attention, `hd : a = a + (c + d)` est dans le « mauvais sens » pour `add_right_eq_self` : utilise `hd.symm`.
-/
import Solutions.Naturels.LeBase
import Solutions.Naturels.AddSelf

/-!
# Antisymétrie

Si `a ≤ b` et `b ≤ a`, alors `a = b`. Avec la réflexivité et la transitivité, ça fait de `≤`
une **relation d'ordre**.

## À prouver
`le_antisymm (a b : ℕ) : a ≤ b → b ≤ a → a = b`
-/

namespace Parcours.ℕ

theorem le_antisymm (a b : ℕ) (hab : a ≤ b) (hba : b ≤ a) : a = b := by -- @exo
  obtain ⟨c, hc⟩ := hab
  obtain ⟨d, hd⟩ := hba
  rw [hc, add_assoc] at hd
  have h := add_right_eq_self a (c + d) hd.symm
  have hc0 := (add_eq_zero c d h).1
  rw [hc, hc0]
  rfl

end Parcours.ℕ

#verifier
