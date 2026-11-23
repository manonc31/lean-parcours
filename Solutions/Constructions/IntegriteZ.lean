/- @parcours
titre: ℤ est intègre (grâce au pont)
difficulte: 2
indice: Applique `versInt` : `versInt (x * y) = versInt x * versInt y = 0`, et dans `Int`, `Int.mul_eq_zero` conclut.
indice: Pour revenir dans `Zr` : `versInt_injective` (et `versInt 0 = 0` par `rfl`).
-/
import Solutions.Constructions.PontZ

/-!
# ℤ est intègre (grâce au pont)

Un produit nul a un facteur nul. Plutôt que de le prouver sur les couples (pénible), on
**transporte** le résultat de `Int` via le pont. C'est toute la puissance des isomorphismes.

## À prouver
`mul_eq_zero (x y : Zr) : x * y = 0 → x = 0 ∨ y = 0`
-/

namespace Parcours.Constructions

theorem Zr.mul_eq_zero (x y : Zr) (h : x * y = 0) : x = 0 ∨ y = 0 := by -- @exo
  have h1 : versInt x * versInt y = 0 := by
    rw [← versInt_mul, h]
    rfl
  rcases Int.mul_eq_zero.mp h1 with h2 | h2
  · left
    exact versInt_injective _ _ (by rw [h2]; rfl)
  · right
    exact versInt_injective _ _ (by rw [h2]; rfl)

end Parcours.Constructions

#verifier
