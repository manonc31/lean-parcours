import Exercices.Circuits.Definitions

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

---
*Exercice* `Circuits.EchangeXor` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Circuits.EchangeXor` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Circuits

theorem echange (a b : Nat) :
    let a₁ := a ^^^ b
    let b₁ := a₁ ^^^ b
    let a₂ := a₁ ^^^ b₁
    a₂ = b ∧ b₁ = a := by
  sorry

end Parcours.Circuits

#verifier
