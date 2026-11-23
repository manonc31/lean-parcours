/- @parcours
titre: Le pont vers les entiers relatifs de Lean
difficulte: 3
genre: pont
indice: `versInt_respecte` : passe dans `Int` (`omega` sait gérer les conversions `↑a` d'un `Nat` vers `Int`).
indice: Injectivité : `obtain ⟨a, b, rfl⟩` pour les deux, `rw [versInt_mk, versInt_mk] at h`, puis `Zr.mk_eq_mk` et `omega`.
indice: Surjectivité : pour `n : Int`, si `0 ≤ n` prends `Zr.mk n.toNat 0`, sinon `Zr.mk 0 (-n).toNat`. `omega` connaît `Int.toNat`.
indice: `versInt_mul` : `simp only [Zr.mul_mk, versInt_mk, Int.natCast_add, Int.natCast_mul]` puis `grind`.
-/
import Solutions.Constructions.AnneauZ

/-!
# 🌉 Le pont vers les entiers relatifs de Lean

`Int` (les entiers relatifs de Lean) et ton `Zr` sont le même objet. La traduction :
`versInt (Zr.mk a b) = a - b`. Prouve que c'est une bijection qui respecte `+` et `×`.

(Ce pont ne débloque rien de nouveau : `Int` est déjà débloqué avec `Nat`. Mais il montre que
ta construction est **la bonne**.)

## À prouver
1. `versInt_respecte` (pour définir `versInt`)
2. `versInt_injective`, `versInt_surjective`
3. `versInt_add`, `versInt_mul`
-/

namespace Parcours.Constructions

theorem versInt_respecte {a b a' b' : Nat} (h : a + b' = a' + b) : (a : Int) - b = a' - b' := by -- @exo
  omega

def versInt : Zr → Int :=
  Quotient.lift (fun p => (p.1 : Int) - p.2) (fun ⟨_, _⟩ ⟨_, _⟩ h => versInt_respecte h)

theorem versInt_mk (a b : Nat) : versInt (Zr.mk a b) = (a : Int) - b := rfl

theorem versInt_injective (x y : Zr) (h : versInt x = versInt y) : x = y := by -- @exo
  obtain ⟨a, b, rfl⟩ := Zr.existe x
  obtain ⟨c, d, rfl⟩ := Zr.existe y
  rw [versInt_mk, versInt_mk] at h
  rw [Zr.mk_eq_mk]
  omega

theorem versInt_surjective (n : Int) : ∃ x, versInt x = n := by -- @exo
  by_cases h : 0 ≤ n
  · exact ⟨Zr.mk n.toNat 0, by rw [versInt_mk]; omega⟩
  · exact ⟨Zr.mk 0 (-n).toNat, by rw [versInt_mk]; omega⟩

theorem versInt_add (x y : Zr) : versInt (x + y) = versInt x + versInt y := by -- @exo
  obtain ⟨a, b, rfl⟩ := Zr.existe x
  obtain ⟨c, d, rfl⟩ := Zr.existe y
  rw [Zr.add_mk, versInt_mk, versInt_mk, versInt_mk]
  omega

theorem versInt_mul (x y : Zr) : versInt (x * y) = versInt x * versInt y := by -- @exo
  obtain ⟨a, b, rfl⟩ := Zr.existe x
  obtain ⟨c, d, rfl⟩ := Zr.existe y
  simp only [Zr.mul_mk, versInt_mk, Int.natCast_add, Int.natCast_mul]
  grind

end Parcours.Constructions

#verifier
