/- @parcours
titre: √2 n'est pas dans ton ℚ
difficulte: 4
requiert: Constructions.CorpsQ
indice: Écris `x = Qr.mk a d`. L'égalité `x * x = 2` devient (produit en croix) `a * a = 2 * (d + 1) * (d + 1)` dans `Int`.
indice: Passe dans `Nat` avec `a.natAbs` : `Int.natAbs_mul_self : ↑(a.natAbs * a.natAbs) = a * a`, puis `Int.ofNat_inj` (ou `omega` après avoir établi l'égalité des conversions).
indice: Conclus avec ton théorème `Parcours.Arith.racine_deux_irrationnelle` (témoins `a.natAbs` et `d + 1`).
-/
import Solutions.Constructions.CorpsQ
import Solutions.Arithmetique.Racine2

/-!
# √2 n'est pas dans ton ℚ

Tu as prouvé (branche Arithmétique) qu'il n'existe pas d'entiers `a, b > 0` avec `a² = 2b²`.
Transporte ce résultat dans **ta** construction des rationnels : aucun `x : Qr` ne vérifie `x² = 2`.
C'est exactement pour ça qu'il faut construire les **réels** !

## À prouver
`racine_deux_pas_rationnelle : ¬∃ x : Qr, x * x = 2`
-/

namespace Parcours.Constructions

theorem racine_deux_pas_rationnelle : ¬∃ x : Qr, x * x = 2 := by -- @exo
  rintro ⟨x, hx⟩
  obtain ⟨a, d, rfl⟩ := Qr.existe x
  rw [Qr.mul_mk, Qr.ofNat_def, Qr.mk_eq_mk] at hx
  simp only [Int.natCast_add, Int.natCast_mul] at hx
  have hnat : ((a.natAbs * a.natAbs : Nat) : Int) = ((2 * ((d + 1) * (d + 1)) : Nat) : Int) := by
    rw [Int.natAbs_mul_self]
    simp only [Int.natCast_add, Int.natCast_mul]
    grind
  have h2 : a.natAbs * a.natAbs = 2 * ((d + 1) * (d + 1)) := Int.ofNat_inj.mp hnat
  exact Parcours.Arith.racine_deux_irrationnelle ⟨a.natAbs, d + 1, by omega, h2⟩

end Parcours.Constructions

#verifier
