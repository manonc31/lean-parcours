/- @parcours
titre: La puissance cinquième
difficulte: 2
requiert: Olympiades.Parite
indice: Raisonne sur le reste de `n` modulo 5 : cinq cas (`omega` fournit la disjonction).
indice: Dans chaque cas : `simp [Nat.mul_mod, h]`.
-/
import Solutions.Arithmetique.Definitions

/-!
# La puissance cinquième

Pour tout entier `n`, `n⁵` et `n` ont le même dernier chiffre ! (Essaie : `2⁵ = 32`, `3⁵ = 243`, `7⁵ = 16807`.)
Ici, la version modulo 5 (c'est le petit théorème de Fermat pour `p = 5`).

## À prouver
`cinquieme (n : Nat) : (n * n * n * n * n) % 5 = n % 5`
-/

namespace Parcours.Olymp

theorem cinquieme (n : Nat) : (n * n * n * n * n) % 5 = n % 5 := by -- @exo
  have : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  rcases this with h | h | h | h | h <;> simp [Nat.mul_mod, h]

end Parcours.Olymp

#verifier
