/- @parcours
titre: ℤ est un anneau commutatif
difficulte: 2
indice: Méthode pour chaque égalité : `obtain ⟨a, b, rfl⟩ := Zr.existe x` (et pareil pour `y`, `z`), puis `rw [Zr.add_mk, …, Zr.mk_eq_mk]`, et il reste une égalité dans `Nat`.
indice: Pour l'addition, `omega` conclut ; pour la multiplication, `grind`.
indice: Pour `0` et `1`, utilise `Zr.zero_def` et `Zr.one_def`.
-/
import Solutions.Constructions.OperationsZ

/-!
# ℤ est un anneau commutatif

Tu as construit `Zr`. Vérifions que c'est bien « les entiers relatifs » : toutes les règles de
calcul sont vraies. La méthode est toujours la même : se ramener à des couples, puis à une
égalité dans `Nat`.

## À prouver
1. `add_comm`, `add_assoc`, `zero_add`, `add_neg` (`x + -x = 0` : **la** nouveauté par rapport à ℕ !)
2. `mul_comm`, `mul_assoc`, `one_mul`, `mul_add`
-/

namespace Parcours.Constructions.Zr

theorem add_comm (x y : Zr) : x + y = y + x := by -- @exo
  obtain ⟨a, b, rfl⟩ := Zr.existe x
  obtain ⟨c, d, rfl⟩ := Zr.existe y
  rw [add_mk, add_mk, mk_eq_mk]
  omega

theorem add_assoc (x y z : Zr) : x + y + z = x + (y + z) := by -- @exo
  obtain ⟨a, b, rfl⟩ := Zr.existe x
  obtain ⟨c, d, rfl⟩ := Zr.existe y
  obtain ⟨e, f, rfl⟩ := Zr.existe z
  rw [add_mk, add_mk, add_mk, add_mk, mk_eq_mk]
  omega

theorem zero_add (x : Zr) : 0 + x = x := by -- @exo
  obtain ⟨a, b, rfl⟩ := Zr.existe x
  rw [zero_def, add_mk, mk_eq_mk]
  omega

theorem add_neg (x : Zr) : x + -x = 0 := by -- @exo
  obtain ⟨a, b, rfl⟩ := Zr.existe x
  rw [neg_mk, add_mk, zero_def, mk_eq_mk]
  omega

theorem mul_comm (x y : Zr) : x * y = y * x := by -- @exo
  obtain ⟨a, b, rfl⟩ := Zr.existe x
  obtain ⟨c, d, rfl⟩ := Zr.existe y
  rw [mul_mk, mul_mk, mk_eq_mk]
  grind

theorem mul_assoc (x y z : Zr) : x * y * z = x * (y * z) := by -- @exo
  obtain ⟨a, b, rfl⟩ := Zr.existe x
  obtain ⟨c, d, rfl⟩ := Zr.existe y
  obtain ⟨e, f, rfl⟩ := Zr.existe z
  rw [mul_mk, mul_mk, mul_mk, mul_mk, mk_eq_mk]
  grind

theorem one_mul (x : Zr) : 1 * x = x := by -- @exo
  obtain ⟨a, b, rfl⟩ := Zr.existe x
  rw [one_def, mul_mk, mk_eq_mk]
  grind

theorem mul_add (x y z : Zr) : x * (y + z) = x * y + x * z := by -- @exo
  obtain ⟨a, b, rfl⟩ := Zr.existe x
  obtain ⟨c, d, rfl⟩ := Zr.existe y
  obtain ⟨e, f, rfl⟩ := Zr.existe z
  rw [add_mk, mul_mk, mul_mk, mul_mk, add_mk, mk_eq_mk]
  grind

end Parcours.Constructions.Zr

#verifier
