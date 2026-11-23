/- @parcours
titre: Échanger deux variables sans troisième
difficulte: 2
indice: Utilise `Nat.xor_assoc`, `Nat.xor_comm`, `Nat.xor_self`, `Nat.xor_zero`, `Nat.zero_xor`.
indice: Pour le premier : `(a ^^^ b) ^^^ b = a ^^^ (b ^^^ b) = a ^^^ 0 = a`.
-/
import Solutions.Circuits.Definitions

/-!
# Échanger deux variables sans troisième

Une astuce célèbre de programmeur : pour échanger `a` et `b` sans variable temporaire,
```
a := a xor b
b := a xor b    -- vaut maintenant l'ancien a
a := a xor b    -- vaut maintenant l'ancien b
```
Prouve que ça marche, pour tous les entiers.

## À prouver
`echange (a b : Nat) : let a₁ := a ^^^ b; let b₁ := a₁ ^^^ b; let a₂ := a₁ ^^^ b₁; a₂ = b ∧ b₁ = a`
-/

namespace Parcours.Circuits

theorem echange (a b : Nat) :
    let a₁ := a ^^^ b
    let b₁ := a₁ ^^^ b
    let a₂ := a₁ ^^^ b₁
    a₂ = b ∧ b₁ = a := by -- @exo
  have hb : a ^^^ b ^^^ b = a := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  refine ⟨?_, hb⟩
  show a ^^^ b ^^^ (a ^^^ b ^^^ b) = b
  rw [hb, Nat.xor_comm a b, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

end Parcours.Circuits

#verifier
