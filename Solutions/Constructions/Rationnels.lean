/- @parcours
titre: Les rationnels
difficulte: 1
genre: cours
-/
import Solutions.Constructions.RelationQ

/-!
# Les rationnels (cours)

`Qr` est le quotient de `Int × Nat` par la relation « produit en croix ».
`Qr.mk a d` représente `a / (d + 1)`.

## Outils
- `Qr.mk_eq_mk : Qr.mk a d = Qr.mk b e ↔ a * (e + 1) = b * (d + 1)`
- `Qr.existe x : ∃ a d, x = Qr.mk a d`
- Pour pousser les conversions `Nat → Int` : `Int.natCast_add`, `Int.natCast_mul`
  (`simp only [Int.natCast_add, Int.natCast_mul]`), puis `grind`.

## Opérations
- `Qr.mk a d + Qr.mk b e = Qr.mk (a(e+1) + b(d+1)) (d + e + d e)` (car `(d+1)(e+1) = (d + e + de) + 1`)
- `Qr.mk a d * Qr.mk b e = Qr.mk (a b) (d + e + d e)`
-/

namespace Parcours.Constructions

instance setoidQ : Setoid (Int × Nat) := ⟨RelQ, ⟨relQ_refl, relQ_symm, relQ_trans⟩⟩

/-- Les rationnels, construits comme quotient. -/
def Qr : Type := Quotient setoidQ

/-- `Qr.mk a d` représente `a / (d + 1)`. -/
def Qr.mk (a : Int) (d : Nat) : Qr := Quotient.mk setoidQ (a, d)

theorem Qr.mk_eq_mk {a b : Int} {d e : Nat} :
    Qr.mk a d = Qr.mk b e ↔ a * ((e : Int) + 1) = b * ((d : Int) + 1) :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound (s := setoidQ) h⟩

theorem Qr.existe (x : Qr) : ∃ a d, x = Qr.mk a d :=
  Quotient.inductionOn x (fun ⟨a, d⟩ => ⟨a, d, rfl⟩)

instance (n : Nat) : OfNat Qr n := ⟨Qr.mk n 0⟩

theorem Qr.ofNat_def (n : Nat) : (OfNat.ofNat n : Qr) = Qr.mk n 0 := rfl

end Parcours.Constructions
