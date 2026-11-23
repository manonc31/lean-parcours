/- @parcours
titre: La puissance
difficulte: 1
genre: cours
requiert: Naturels.MulAssoc, Naturels.MulComm
-/
import Solutions.Naturels.Multiplication

/-!
# La puissance (cours)

Toujours par récurrence sur le second argument :
- `a ^ 0 = 1`                    (`pow_zero`)
- `a ^ succ b = a ^ b * a`       (`pow_succ`)

Remarque : quand l'exposant est un nombre écrit en chiffres, précise son type : `a ^ (2 : ℕ)`.
Sinon Lean croit que `2` est un entier de sa bibliothèque (`Nat`), et ne trouve pas de puissance `ℕ ^ Nat`.
-/

namespace Parcours.ℕ

/-- La puissance, par récurrence sur l'exposant. -/
def pow : ℕ → ℕ → ℕ
  | _, zero => 1
  | a, succ b => pow a b * a

instance instPow : HPow ℕ ℕ ℕ := ⟨pow⟩

theorem pow_zero (a : ℕ) : a ^ (0 : ℕ) = 1 := rfl
theorem pow_succ (a b : ℕ) : a ^ succ b = a ^ b * a := rfl

end Parcours.ℕ
