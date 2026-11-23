import Exercices.Constructions.OperationsZ

/-!
# L'ordre sur ℤ

On définit `Zr.mk a b ≤ Zr.mk c d` par `a + d ≤ c + b`. Encore une fois, il faut vérifier que
c'est bien défini (indépendant des représentants), puis que c'est un ordre total compatible avec `+`.

## À prouver
1. `le_respecte` (pour définir `≤`)
2. `le_refl`, `le_trans`, `le_total`
3. `add_le_add_gauche : x ≤ y → z + x ≤ z + y`

---
*Exercice* `Constructions.OrdreZ` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Constructions.OrdreZ` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Constructions

theorem le_respecte {a b c d a' b' c' d' : Nat} (h1 : a + b' = a' + b) (h2 : c + d' = c' + d) :
    (a + d ≤ c + b) = (a' + d' ≤ c' + b') := by
  sorry

def Zr.le : Zr → Zr → Prop :=
  Quotient.lift₂ (fun p q => p.1 + q.2 ≤ q.1 + p.2)
    (fun ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ h1 h2 => le_respecte h1 h2)

instance : LE Zr := ⟨Zr.le⟩

theorem Zr.le_mk (a b c d : Nat) : Zr.mk a b ≤ Zr.mk c d ↔ a + d ≤ c + b := Iff.rfl

namespace Zr

theorem le_refl (x : Zr) : x ≤ x := by
  sorry

theorem le_trans (x y z : Zr) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  sorry

theorem le_total (x y : Zr) : x ≤ y ∨ y ≤ x := by
  sorry

theorem add_le_add_gauche (x y z : Zr) (h : x ≤ y) : z + x ≤ z + y := by
  sorry

end Zr
end Parcours.Constructions

#verifier
