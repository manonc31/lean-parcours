/- @parcours
titre: La fonction d'Ackermann
difficulte: 3
requiert: Recurrence.Croissance
indice: `simp only [ack]` déplie la définition d'un cran (Lean a généré les équations).
indice: `ack_un` et `ack_deux` : récurrence sur `n`, puis `simp only [ack, ih, …]` et `omega`.
indice: `ack_trois` : `ack 3 (n + 1) = ack 2 (ack 3 n)`. Il te faudra `Nat.pow_succ` et le fait que `8 ≤ 2 ^ (n + 3)` (`Nat.pow_le_pow_right`).
indice: `lt_ack` : récurrence sur `m` en généralisant `n`, puis récurrence sur `n` à l'intérieur.
-/
import Solutions.Recurrence.Definitions

/-!
# La fonction d'Ackermann

```
ack 0 n = n + 1
ack (m+1) 0 = ack m 1
ack (m+1) (n+1) = ack m (ack (m+1) n)
```

Elle termine toujours (Lean l'a vérifié avec un ordre **lexicographique** sur `(m, n)`), mais elle
grandit à une vitesse vertigineuse : `ack 4 2` a 19 729 chiffres. C'est l'exemple historique
(1928) d'une fonction calculable qui n'est pas « récursive primitive » (aucune boucle `for` ne suffit).

## À prouver
1. `ack_un : ack 1 n = n + 2`
2. `ack_deux : ack 2 n = 2 * n + 3`
3. `ack_trois : ack 3 n = 2 ^ (n + 3) - 3`
4. `lt_ack : n < ack m n`

## Ressources
- [Fonction d'Ackermann (Wikipédia)](https://fr.wikipedia.org/wiki/Fonction_d%27Ackermann)
-/

namespace Parcours.Term

def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)

theorem ack_un (n : Nat) : ack 1 n = n + 2 := by -- @exo
  induction n with
  | zero => simp [ack]
  | succ n ih => simp only [ack, ih]

theorem ack_deux (n : Nat) : ack 2 n = 2 * n + 3 := by -- @exo
  induction n with
  | zero => simp [ack, ack_un]
  | succ n ih =>
    simp only [ack, ih, ack_un]
    omega

theorem ack_trois (n : Nat) : ack 3 n = 2 ^ (n + 3) - 3 := by -- @exo
  induction n with
  | zero => simp [ack, ack_deux]
  | succ n ih =>
    rw [show ack 3 (n + 1) = ack 2 (ack 3 n) by simp only [ack], ack_deux, ih]
    have h8 : 2 ^ 3 ≤ 2 ^ (n + 3) := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : (2 : Nat) ^ 3 = 8 := rfl
    have hp : 2 ^ (n + 1 + 3) = 2 * 2 ^ (n + 3) := by
      rw [show n + 1 + 3 = (n + 3) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    omega

theorem lt_ack (m n : Nat) : n < ack m n := by -- @exo
  induction m generalizing n with
  | zero => simp [ack]
  | succ m ihm =>
    induction n with
    | zero =>
      simp only [ack]
      have := ihm 1
      omega
    | succ n ihn =>
      simp only [ack]
      have := ihm (ack (m + 1) n)
      omega

end Parcours.Term

#verifier
