/- @parcours
titre: Une récurrence sur Nat
difficulte: 2
requiert: Gymnase.Omega
indice: `induction n with | zero => rfl | succ n ih => …`.
indice: Cas `succ` : `rw [double, ih]` puis `omega`.
-/
import Solutions.Naturels.Transfert

/-!
# Une récurrence sur Nat

On définit `double n` par récurrence (`double 0 = 0`, `double (n+1) = double n + 2`). Prouve que `double n = 2 * n` : `induction n with`, puis dans le cas `succ`, déplie la définition (`rw [double]` ou `simp only [double]`) et utilise `ih` et `omega`.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

def double : Nat → Nat
  | 0 => 0
  | n + 1 => double n + 2

theorem double_eq (n : Nat) : double n = 2 * n := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [double, ih]
    omega

end Parcours.Gymnase

#verifier
