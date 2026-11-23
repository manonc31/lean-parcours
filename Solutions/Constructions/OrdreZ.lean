/- @parcours
titre: L'ordre sur ℤ
difficulte: 3
indice: `(a, b) ≤ (c, d)` signifie « `a - b ≤ c - d` », c'est-à-dire `a + d ≤ c + b`. La compatibilité se fait avec `omega`… mais attention, c'est une **équivalence** de propositions (`propext` est utilisé dans la définition).
indice: Pour les propriétés : `obtain ⟨a, b, rfl⟩ := Zr.existe x`, puis `rw [le_mk]` (ou `le_mk` en `.mpr`/`.mp`), puis `omega`.
-/
import Solutions.Constructions.OperationsZ

/-!
# L'ordre sur ℤ

On définit `Zr.mk a b ≤ Zr.mk c d` par `a + d ≤ c + b`. Encore une fois, il faut vérifier que
c'est bien défini (indépendant des représentants), puis que c'est un ordre total compatible avec `+`.

## À prouver
1. `le_respecte` (pour définir `≤`)
2. `le_refl`, `le_trans`, `le_total`
3. `add_le_add_gauche : x ≤ y → z + x ≤ z + y`
-/

namespace Parcours.Constructions

theorem le_respecte {a b c d a' b' c' d' : Nat} (h1 : a + b' = a' + b) (h2 : c + d' = c' + d) :
    (a + d ≤ c + b) = (a' + d' ≤ c' + b') := by -- @exo
  apply propext
  omega

def Zr.le : Zr → Zr → Prop :=
  Quotient.lift₂ (fun p q => p.1 + q.2 ≤ q.1 + p.2)
    (fun ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ h1 h2 => le_respecte h1 h2)

instance : LE Zr := ⟨Zr.le⟩

theorem Zr.le_mk (a b c d : Nat) : Zr.mk a b ≤ Zr.mk c d ↔ a + d ≤ c + b := Iff.rfl

namespace Zr

theorem le_refl (x : Zr) : x ≤ x := by -- @exo
  obtain ⟨a, b, rfl⟩ := Zr.existe x
  rw [le_mk]
  omega

theorem le_trans (x y z : Zr) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by -- @exo
  obtain ⟨a, b, rfl⟩ := Zr.existe x
  obtain ⟨c, d, rfl⟩ := Zr.existe y
  obtain ⟨e, f, rfl⟩ := Zr.existe z
  rw [le_mk] at *
  omega

theorem le_total (x y : Zr) : x ≤ y ∨ y ≤ x := by -- @exo
  obtain ⟨a, b, rfl⟩ := Zr.existe x
  obtain ⟨c, d, rfl⟩ := Zr.existe y
  rw [le_mk, le_mk]
  omega

theorem add_le_add_gauche (x y z : Zr) (h : x ≤ y) : z + x ≤ z + y := by -- @exo
  obtain ⟨a, b, rfl⟩ := Zr.existe x
  obtain ⟨c, d, rfl⟩ := Zr.existe y
  obtain ⟨e, f, rfl⟩ := Zr.existe z
  rw [add_mk, add_mk, le_mk]
  rw [le_mk] at h
  omega

end Zr
end Parcours.Constructions

#verifier
