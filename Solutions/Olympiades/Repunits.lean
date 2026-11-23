/- @parcours
titre: 11, 111, 1111… ne sont jamais des carrés
difficulte: 3
requiert: Olympiades.Parite
indice: `carre_mod_quatre` : quatre cas selon `k % 4`, puis `simp [Nat.mul_mod, h]`.
indice: `repunit_mod_quatre` : récurrence ; `repunit (m + 1) = 10 * repunit m + 1`, et `omega`.
-/
import Solutions.Arithmetique.Definitions

/-!
# 11, 111, 1111… ne sont jamais des carrés

Les **répunits** sont les nombres qui ne s'écrivent qu'avec des 1. Aucun (à part 1) n'est un carré !

## Se le représenter
Un carré vaut 0 ou 1 modulo 4 (pair : `(2k)² = 4k²` ; impair : `(2k+1)² = 4k² + 4k + 1`). Or
`11…11 = 11…00 + 11` et `100` est multiple de 4 : un répunit d'au moins deux chiffres vaut
`11 ≡ 3 (mod 4)`.

## À prouver
1. `carre_mod_quatre : k * k % 4 = 0 ∨ k * k % 4 = 1`
2. `repunit_mod_quatre : repunit (n + 2) % 4 = 3`
3. `repunit_pas_carre : k * k ≠ repunit (n + 2)`
-/

namespace Parcours.Olymp

def repunit : Nat → Nat
  | 0 => 0
  | n + 1 => 10 * repunit n + 1

theorem carre_mod_quatre (k : Nat) : k * k % 4 = 0 ∨ k * k % 4 = 1 := by -- @exo
  have : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases this with h | h | h | h <;> simp [Nat.mul_mod, h]

theorem repunit_mod_quatre (n : Nat) : repunit (n + 2) % 4 = 3 := by -- @exo
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 from rfl, repunit]
    omega

theorem repunit_pas_carre (n k : Nat) : k * k ≠ repunit (n + 2) := by -- @exo
  intro h
  have h1 := carre_mod_quatre k
  have h2 := repunit_mod_quatre n
  omega

end Parcours.Olymp

#verifier
