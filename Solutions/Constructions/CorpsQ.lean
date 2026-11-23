/- @parcours
debloque: Rat
titre: ℚ est un corps
difficulte: 3
indice: Pour les égalités : `obtain ⟨a, d, rfl⟩ := Qr.existe x` (etc.), `rw [Qr.add_mk, …, Qr.mk_eq_mk]`, `simp only [Int.natCast_add, Int.natCast_mul]`, `grind`.
indice: Inverse : si `x = Qr.mk a d` et `x ≠ 0`, alors `a ≠ 0`. Écris `a = n + 1` ou `a = -(n + 1)` avec `n : Nat` (`omega` aide à construire `n` : `⟨a.toNat - 1, by omega⟩`).
indice: Si `a = n + 1`, l'inverse est `Qr.mk (d + 1) n` (c'est `(d+1)/(n+1)`). Si `a = -(n+1)`, c'est `Qr.mk (-(d + 1)) n`.
-/
import Solutions.Constructions.OperationsQ

/-!
# ℚ est un corps

La grande nouveauté de ℚ : on peut **diviser**. Tout rationnel non nul a un inverse.

🔑 **Récompense** : une fois ℚ construit de tes mains, cet exercice débloque le jeton **`Rat`** :
les rationnels de Lean (`Rat`) et leurs lemmes deviennent purs pour la suite (branche Analyse).

## À prouver
1. `add_comm`, `mul_comm`, `mul_add`
2. `inverse (x : Qr) (hx : x ≠ 0) : ∃ y, x * y = 1`
-/

namespace Parcours.Constructions.Qr

theorem add_comm (x y : Qr) : x + y = y + x := by -- @exo
  obtain ⟨a, d, rfl⟩ := Qr.existe x
  obtain ⟨b, e, rfl⟩ := Qr.existe y
  rw [add_mk, add_mk, mk_eq_mk]
  simp only [Int.natCast_add, Int.natCast_mul]
  grind

theorem mul_comm (x y : Qr) : x * y = y * x := by -- @exo
  obtain ⟨a, d, rfl⟩ := Qr.existe x
  obtain ⟨b, e, rfl⟩ := Qr.existe y
  rw [mul_mk, mul_mk, mk_eq_mk]
  simp only [Int.natCast_add, Int.natCast_mul]
  grind

theorem mul_add (x y z : Qr) : x * (y + z) = x * y + x * z := by -- @exo
  obtain ⟨a, d, rfl⟩ := Qr.existe x
  obtain ⟨b, e, rfl⟩ := Qr.existe y
  obtain ⟨c, f, rfl⟩ := Qr.existe z
  rw [add_mk, mul_mk, mul_mk, mul_mk, add_mk, mk_eq_mk]
  simp only [Int.natCast_add, Int.natCast_mul]
  grind

theorem inverse (x : Qr) (hx : x ≠ 0) : ∃ y, x * y = 1 := by -- @exo
  obtain ⟨a, d, rfl⟩ := Qr.existe x
  have ha : a ≠ 0 := by
    intro h
    apply hx
    rw [h, ofNat_def, mk_eq_mk]
    simp
  rcases Int.lt_or_gt_of_ne ha with hneg | hpos
  · obtain ⟨n, hn⟩ : ∃ n : Nat, a = -((n : Int) + 1) := ⟨(-a).toNat - 1, by omega⟩
    refine ⟨Qr.mk (-((d : Int) + 1)) n, ?_⟩
    rw [mul_mk, ofNat_def, mk_eq_mk, hn]
    simp only [Int.natCast_add, Int.natCast_mul]
    grind
  · obtain ⟨n, hn⟩ : ∃ n : Nat, a = (n : Int) + 1 := ⟨a.toNat - 1, by omega⟩
    refine ⟨Qr.mk ((d : Int) + 1) n, ?_⟩
    rw [mul_mk, ofNat_def, mk_eq_mk, hn]
    simp only [Int.natCast_add, Int.natCast_mul]
    grind

end Parcours.Constructions.Qr

#verifier
