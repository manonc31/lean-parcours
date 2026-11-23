/- @parcours
titre: Changer de base
difficulte: 3
requiert: Programmes.Chiffres
indice: `fun_induction versBase b n` : deux cas.
indice: `Nat.mod_add_div n b : n % b + b * (n / b) = n`.
indice: Pour `chiffres_petits` : `Nat.mod_lt`.
-/
import Solutions.Programmes.Definitions

/-!
# Changer de base

Écrire un nombre en base `b` : les chiffres sont les restes successifs de la division par `b`
(chiffre des unités en tête). Puis relire la liste de chiffres pour retrouver le nombre.
`versBase 2 13 = [1, 0, 1, 1]` (car 13 = 1101 en binaire).

## À prouver
1. `aller_retour : depuisBase b (versBase b n) = n` (pour `b ≥ 2`)
2. `chiffres_petits : d ∈ versBase b n → d < b`
-/

namespace Parcours.Prog

def versBase (b n : Nat) : List Nat :=
  if h : 2 ≤ b ∧ 0 < n then n % b :: versBase b (n / b) else []
termination_by n
decreasing_by exact Nat.div_lt_self h.2 (by omega)

def depuisBase (b : Nat) : List Nat → Nat
  | [] => 0
  | d :: l => d + b * depuisBase b l

theorem aller_retour (b n : Nat) (hb : 2 ≤ b) : depuisBase b (versBase b n) = n := by -- @exo
  fun_induction versBase b n with
  | case1 n h ih =>
    simp only [depuisBase, ih]
    exact Nat.mod_add_div n b
  | case2 n h =>
    simp only [depuisBase]
    omega

theorem chiffres_petits (b n : Nat) : ∀ d ∈ versBase b n, d < b := by -- @exo
  fun_induction versBase b n with
  | case1 n h ih =>
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact Nat.mod_lt _ (by omega)
    · exact ih d hd
  | case2 n h => simp

end Parcours.Prog

#verifier
