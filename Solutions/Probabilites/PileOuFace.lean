/- @parcours
titre: Pile ou face et le triangle de Pascal
difficulte: 4
indice: `longueur_mots` : récurrence ; `List.length_append`, `List.length_map`, `Nat.pow_succ`.
indice: `nombre_de_piles` : récurrence sur `n` en généralisant `k`. Les mots de longueur `n + 1` sont `false :: w` et `true :: w` : `List.countP_append` et `List.countP_map`.
indice: Le nombre de `true` dans `true :: w` est `w.count true + 1`. Avec `k = 0` et `k = j + 1` séparés (`cases k`), on retrouve la formule de Pascal `binom_succ_succ`.
-/
import Solutions.Probabilites.Definitions

/-!
# Pile ou face et le triangle de Pascal

On lance `n` fois une pièce. Il y a `2ⁿ` suites possibles, et exactement `C(n, k)` d'entre elles
contiennent `k` « pile ». Donc `P(k piles) = C(n, k) / 2ⁿ` : c'est la **loi binomiale**.

`mots n` est la liste de tous les mots de longueur `n` sur `{false, true}` (`true` = pile).

## À prouver
1. `longueur_mots : (mots n).length = 2 ^ n`
2. `nombre_de_piles : (mots n).countP (fun w => w.count true == k) = binom n k`

## Ressources
- [Loi binomiale (Wikipédia)](https://fr.wikipedia.org/wiki/Loi_binomiale)
-/

namespace Parcours.Proba

open Parcours.Combi

def mots : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (mots n).map (false :: ·) ++ (mots n).map (true :: ·)

theorem longueur_mots (n : Nat) : (mots n).length = 2 ^ n := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [mots, List.length_append, List.length_map, ih, Nat.pow_succ]
    omega

theorem nombre_de_piles (n k : Nat) :
    (mots n).countP (fun w => w.count true == k) = binom n k := by -- @exo
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => rfl
    | succ k => rfl
  | succ n ih =>
    simp only [mots, List.countP_append, List.countP_map]
    have e1 : (mots n).countP ((fun w => w.count true == k) ∘ (false :: ·)) =
        (mots n).countP (fun w => w.count true == k) := by
      congr 1
    rw [e1, ih]
    cases k with
    | zero =>
      have e2 : (mots n).countP ((fun w => w.count true == 0) ∘ (true :: ·)) = 0 := by
        rw [List.countP_eq_zero]
        intro w _
        simp [Function.comp]
      rw [e2, binom_zero_droite, binom_zero_droite]
    | succ j =>
      have e2 : (mots n).countP ((fun w => w.count true == j + 1) ∘ (true :: ·)) =
          (mots n).countP (fun w => w.count true == j) := by
        congr 1
        funext w
        simp [Function.comp, List.count_cons]
      rw [e2, ih, binom_succ_succ, Nat.add_comm]

end Parcours.Proba

#verifier
