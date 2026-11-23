/- @parcours
titre: La multiplication
difficulte: 1
genre: cours
requiert: Naturels.AddComm, Naturels.AddRightComm, Naturels.AddSelf
-/
import Solutions.Naturels.Base

/-!
# La multiplication (cours)

Comme l'addition, la multiplication est définie par récurrence sur le second argument :
- `a * 0 = 0`                   (`mul_zero`)
- `a * succ b = a * b + a`      (`mul_succ`)

C'est-à-dire : `a × (b + 1) = a × b + a`. Tout le reste (commutativité, associativité,
distributivité…) sera prouvé par toi.

## Ressources
- [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4), monde « Multiplication ».
-/

namespace Parcours.ℕ

/-- La multiplication, par récurrence sur le second argument. -/
def mul : ℕ → ℕ → ℕ
  | _, zero => 0
  | a, succ b => mul a b + a

instance : Mul ℕ := ⟨mul⟩

theorem mul_zero (a : ℕ) : a * 0 = 0 := rfl
theorem mul_succ (a b : ℕ) : a * succ b = a * b + a := rfl

end Parcours.ℕ
