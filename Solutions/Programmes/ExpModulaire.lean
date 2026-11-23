/- @parcours
titre: L'exponentiation modulaire
difficulte: 3
requiert: Programmes.Russe
indice: `fun_induction expMod a n m` : trois cas.
indice: `Nat.mul_mod : a * b % n = (a % n) * (b % n) % n` (à utiliser de droite à gauche), `Nat.pow_add`, `Nat.pow_succ`.
indice: À la fin, `n / 2 + n / 2 = n` (ou `+ 1`) : `congr 2` puis `omega`.
-/
import Solutions.Programmes.Definitions

/-!
# L'exponentiation modulaire

Pour calculer `a^n mod m` avec des nombres géants (c'est le cœur de RSA), on ne calcule jamais
`a^n` : on réduit modulo `m` à chaque étape, et on utilise `a^(2k) = (a^k)²`.

## À prouver
`expMod_spec : expMod a n m = a ^ n % m`

## Ressources
- [Exponentiation modulaire (Wikipédia)](https://fr.wikipedia.org/wiki/Exponentiation_modulaire)
-/

namespace Parcours.Prog

def expMod (a n m : Nat) : Nat :=
  if n = 0 then 1 % m
  else if n % 2 = 0 then (expMod a (n / 2) m * expMod a (n / 2) m) % m
  else (expMod a (n / 2) m * expMod a (n / 2) m * a) % m
termination_by n
decreasing_by all_goals omega

theorem expMod_spec (a n m : Nat) : expMod a n m = a ^ n % m := by -- @exo
  fun_induction expMod a n m with
  | case1 => simp
  | case2 n h1 h2 ih =>
    rw [ih, ← Nat.mul_mod, ← Nat.pow_add]
    congr 2
    omega
  | case3 n h1 h2 ih =>
    rw [ih, Nat.mul_mod, ← Nat.mul_mod (a ^ (n / 2)), ← Nat.mul_mod, ← Nat.pow_add, ← Nat.pow_succ]
    congr 2
    omega

end Parcours.Prog

#verifier
