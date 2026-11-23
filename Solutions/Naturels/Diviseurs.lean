/- @parcours
titre: La divisibilité dans ℕ
difficulte: 2
indice: `divise_refl` : `⟨1, (mul_one a).symm⟩`.
indice: `divise_trans` : `obtain ⟨k, rfl⟩ := h1`, `obtain ⟨l, rfl⟩ := h2`, puis `⟨k * l, mul_assoc a k l⟩`.
indice: `divise_add` : témoin `k + l` et `mul_add`.
-/
import Solutions.Naturels.MulAssoc
import Solutions.Naturels.MulBase

/-!
# La divisibilité dans ℕ

`a ∣ b` (« `a` divise `b` ») : il existe `c` avec `b = a × c`. Sur **ton** ℕ de Peano, avec
**tes** lemmes. (On refera tout plus loin, en grand, dans la branche Arithmétique.)

## À prouver
1. `divise_refl : Divise a a`
2. `divise_trans : Divise a b → Divise b c → Divise a c`
3. `divise_add : Divise a b → Divise a c → Divise a (b + c)`
4. `un_divise : Divise 1 a`
-/

namespace Parcours.ℕ

def Divise (a b : ℕ) : Prop := ∃ c, b = a * c

theorem divise_refl (a : ℕ) : Divise a a := by -- @exo
  exact ⟨1, (mul_one a).symm⟩

theorem divise_trans {a b c : ℕ} (h1 : Divise a b) (h2 : Divise b c) : Divise a c := by -- @exo
  obtain ⟨k, rfl⟩ := h1
  obtain ⟨l, rfl⟩ := h2
  exact ⟨k * l, mul_assoc a k l⟩

theorem divise_add {a b c : ℕ} (h1 : Divise a b) (h2 : Divise a c) : Divise a (b + c) := by -- @exo
  obtain ⟨k, rfl⟩ := h1
  obtain ⟨l, rfl⟩ := h2
  exact ⟨k + l, (mul_add a k l).symm⟩

theorem un_divise (a : ℕ) : Divise 1 a := by -- @exo
  exact ⟨a, (one_mul a).symm⟩

end Parcours.ℕ

#verifier
