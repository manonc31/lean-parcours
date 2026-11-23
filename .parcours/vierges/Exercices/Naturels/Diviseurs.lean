import Exercices.Naturels.MulAssoc
import Exercices.Naturels.MulBase

/-!
# La divisibilité dans ℕ

`a ∣ b` (« `a` divise `b` ») : il existe `c` avec `b = a × c`. Sur **ton** ℕ de Peano, avec
**tes** lemmes. (On refera tout plus loin, en grand, dans la branche Arithmétique.)

## À prouver
1. `divise_refl : Divise a a`
2. `divise_trans : Divise a b → Divise b c → Divise a c`
3. `divise_add : Divise a b → Divise a c → Divise a (b + c)`
4. `un_divise : Divise 1 a`

---
*Exercice* `Naturels.Diviseurs` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Naturels.Diviseurs` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

def Divise (a b : ℕ) : Prop := ∃ c, b = a * c

theorem divise_refl (a : ℕ) : Divise a a := by
  sorry

theorem divise_trans {a b c : ℕ} (h1 : Divise a b) (h2 : Divise b c) : Divise a c := by
  sorry

theorem divise_add {a b c : ℕ} (h1 : Divise a b) (h2 : Divise a c) : Divise a (b + c) := by
  sorry

theorem un_divise (a : ℕ) : Divise 1 a := by
  sorry

end Parcours.ℕ

#verifier
