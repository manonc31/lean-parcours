/- @parcours
titre: Les opérations sur ℚ
difficulte: 3
indice: Commence par `simp only [Int.natCast_add, Int.natCast_mul]` pour transformer `↑(d + e + d * e)` en `↑d + ↑e + ↑d * ↑e`.
indice: Puis `grind` combine les deux hypothèses de produit en croix.
-/
import Solutions.Constructions.Rationnels

/-!
# Les opérations sur ℚ

Comme pour ℤ : définir `+` et `×` sur les fractions, en prouvant que le résultat ne dépend pas
des représentants (`1/2 + 1/3` doit être égal à `2/4 + 3/9`).

## À prouver
1. `addQ_respecte`
2. `mulQ_respecte`
-/

namespace Parcours.Constructions

theorem addQ_respecte {a b a' b' : Int} {d e d' e' : Nat}
    (h1 : a * ((d' : Int) + 1) = a' * ((d : Int) + 1))
    (h2 : b * ((e' : Int) + 1) = b' * ((e : Int) + 1)) :
    (a * ((e : Int) + 1) + b * ((d : Int) + 1)) * (((d' + e' + d' * e' : Nat) : Int) + 1) =
      (a' * ((e' : Int) + 1) + b' * ((d' : Int) + 1)) * (((d + e + d * e : Nat) : Int) + 1) := by -- @exo
  simp only [Int.natCast_add, Int.natCast_mul]
  grind

theorem mulQ_respecte {a b a' b' : Int} {d e d' e' : Nat}
    (h1 : a * ((d' : Int) + 1) = a' * ((d : Int) + 1))
    (h2 : b * ((e' : Int) + 1) = b' * ((e : Int) + 1)) :
    (a * b) * (((d' + e' + d' * e' : Nat) : Int) + 1) =
      (a' * b') * (((d + e + d * e : Nat) : Int) + 1) := by -- @exo
  simp only [Int.natCast_add, Int.natCast_mul]
  grind

def Qr.add : Qr → Qr → Qr :=
  Quotient.lift₂ (fun p q => Qr.mk (p.1 * ((q.2 : Int) + 1) + q.1 * ((p.2 : Int) + 1)) (p.2 + q.2 + p.2 * q.2))
    (fun ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ h1 h2 => Qr.mk_eq_mk.mpr (addQ_respecte h1 h2))

def Qr.mul : Qr → Qr → Qr :=
  Quotient.lift₂ (fun p q => Qr.mk (p.1 * q.1) (p.2 + q.2 + p.2 * q.2))
    (fun ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ h1 h2 => Qr.mk_eq_mk.mpr (mulQ_respecte h1 h2))

instance : Add Qr := ⟨Qr.add⟩
instance : Mul Qr := ⟨Qr.mul⟩

theorem Qr.add_mk (a b : Int) (d e : Nat) :
    Qr.mk a d + Qr.mk b e = Qr.mk (a * ((e : Int) + 1) + b * ((d : Int) + 1)) (d + e + d * e) := rfl
theorem Qr.mul_mk (a b : Int) (d e : Nat) :
    Qr.mk a d * Qr.mk b e = Qr.mk (a * b) (d + e + d * e) := rfl

end Parcours.Constructions

#verifier
