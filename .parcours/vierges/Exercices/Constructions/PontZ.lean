import Exercices.Constructions.AnneauZ

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

---
*Exercice* `Constructions.PontZ` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Constructions.PontZ` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Constructions

theorem versInt_respecte {a b a' b' : Nat} (h : a + b' = a' + b) : (a : Int) - b = a' - b' := by
  sorry

def versInt : Zr → Int :=
  Quotient.lift (fun p => (p.1 : Int) - p.2) (fun ⟨_, _⟩ ⟨_, _⟩ h => versInt_respecte h)

theorem versInt_mk (a b : Nat) : versInt (Zr.mk a b) = (a : Int) - b := rfl

theorem versInt_injective (x y : Zr) (h : versInt x = versInt y) : x = y := by
  sorry

theorem versInt_surjective (n : Int) : ∃ x, versInt x = n := by
  sorry

theorem versInt_add (x y : Zr) : versInt (x + y) = versInt x + versInt y := by
  sorry

theorem versInt_mul (x y : Zr) : versInt (x * y) = versInt x * versInt y := by
  sorry

end Parcours.Constructions

#verifier
