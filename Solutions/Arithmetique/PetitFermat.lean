/- @parcours
titre: Le petit théorème de Fermat
difficulte: 4
indice: « Rêve de l'étudiant » : développe `(a + b)^p` avec `binome`. Sors le premier terme (`somme_decale`) et le dernier (`somme_succ`) : ils valent `b^p` et `a^p`.
indice: Tous les termes du milieu contiennent `binom p (k+1)` avec `0 < k + 1 < p` : divisibles par `p` (`divise_somme`, `premier_divise_binom`).
indice: Pour conclure modulo `p` : `Nat.add_mul_mod_self_left : (x + y * z) % y = x % y`.
indice: Fermat : récurrence sur `a`. `(a + 1)^p ≡ a^p + 1 ≡ a + 1`, avec `congru_trans` et `congru_add`.
-/
import Solutions.Arithmetique.BinomPremier
import Solutions.Arithmetique.Congruences
import Solutions.Combinatoire.Newton

/-!
# Le petit théorème de Fermat

> Si `p` est premier, alors `aᵖ ≡ a (mod p)` pour tout entier `a`.

Énoncé par Fermat en 1640 (« je vous en envoierois la démonstration, si je n'appréhendois d'être
trop long »), prouvé par Euler en 1736. C'est la base du chiffrement **RSA** et des tests de primalité.

La preuve passe par le « rêve de l'étudiant » : modulo `p`, `(a + b)ᵖ ≡ aᵖ + bᵖ` !

## À prouver
1. `reve_etudiant : Premier p → (a + b) ^ p ≡ a ^ p + b ^ p [mod p]`
2. `petit_fermat : Premier p → a ^ p ≡ a [mod p]`

## Ressources
- [Petit théorème de Fermat (Wikipédia)](https://fr.wikipedia.org/wiki/Petit_th%C3%A9or%C3%A8me_de_Fermat)
- [Chiffrement RSA (Wikipédia)](https://fr.wikipedia.org/wiki/Chiffrement_RSA)
-/

namespace Parcours.Arith

open Parcours.Combi

theorem reve_etudiant {p : Nat} (hp : Premier p) (a b : Nat) :
    (a + b) ^ p ≡ a ^ p + b ^ p [mod p] := by -- @exo
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.1; omega⟩
  have h1 : (a + b) ^ (q + 1) = b ^ (q + 1) +
      somme (fun k => binom (q + 1) (k + 1) * a ^ (k + 1) * b ^ (q + 1 - (k + 1))) q + a ^ (q + 1) := by
    rw [binome, somme_decale, somme_succ]
    simp [binom_zero_droite, binom_self, Nat.add_assoc]
  have hmid : (q + 1) ∣ somme (fun k => binom (q + 1) (k + 1) * a ^ (k + 1) * b ^ (q + 1 - (k + 1))) q := by
    apply divise_somme
    intro k hk
    exact divise_mul_droite (divise_mul_droite (premier_divise_binom hp (by omega) (by omega)) _) _
  obtain ⟨m, hm⟩ := hmid
  show (a + b) ^ (q + 1) % (q + 1) = (a ^ (q + 1) + b ^ (q + 1)) % (q + 1)
  rw [h1, hm, show b ^ (q + 1) + (q + 1) * m + a ^ (q + 1) = a ^ (q + 1) + b ^ (q + 1) + (q + 1) * m by omega]
  exact Nat.add_mul_mod_self_left _ _ _

theorem petit_fermat {p : Nat} (hp : Premier p) (a : Nat) : a ^ p ≡ a [mod p] := by -- @exo
  induction a with
  | zero =>
    show 0 ^ p % p = 0 % p
    rw [Nat.zero_pow (by have := hp.1; omega)]
  | succ a ih =>
    have h := reve_etudiant hp a 1
    rw [Nat.one_pow] at h
    exact congru_trans h (congru_add ih (congru_refl p 1))

end Parcours.Arith

#verifier
