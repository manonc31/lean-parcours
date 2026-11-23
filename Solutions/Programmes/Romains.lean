/- @parcours
titre: Les chiffres romains
difficulte: 2
requiert: Programmes.Bases
indice: `lire` se définit par cas : liste vide, un seul chiffre, ou deux chiffres `a :: b :: r` (on compare `a.val` et `b.val`).
indice: Attention : dans `IX`, on calcule `lire [X] − 1`.
indice: Les preuves sont des calculs : `decide +kernel` vérifie les 4000 nombres.
-/
import Solutions.Programmes.Definitions

/-!
# Les chiffres romains

`MMXXIV` = 2024. Écrire en chiffres romains se fait de façon **gloutonne** avec les briques
`M = 1000, CM = 900, D = 500, CD = 400, C = 100, XC = 90, L, XL, X, IX, V, IV, I`. Le programme
`romain` est donné.

**À toi d'écrire la lecture** `lire` : un chiffre suivi d'un chiffre **plus grand** se soustrait
(`IX = 9`), sinon il s'ajoute (`XI = 11`).

## À faire
1. Écris `lire` ;
2. prouve `exemples_romains` et `aller_retour_romain : n < 4000 → lire (romain n) = n`. (Pour que le noyau de
   Lean ne s'essouffle pas, on vérifie d'abord les nombres par paquets de 100.)

## Ressources
- [Numération romaine (Wikipédia)](https://fr.wikipedia.org/wiki/Num%C3%A9ration_romaine)
-/

namespace Parcours.Prog

inductive Chiffre where
  | I | V | X | L | C | D | M
  deriving DecidableEq

def Chiffre.val : Chiffre → Nat
  | .I => 1 | .V => 5 | .X => 10 | .L => 50 | .C => 100 | .D => 500 | .M => 1000

open Chiffre in
def briques : List (Nat × List Chiffre) :=
  [(1000, [M]), (900, [C, M]), (500, [D]), (400, [C, D]), (100, [C]), (90, [X, C]), (50, [L]),
   (40, [X, L]), (10, [X]), (9, [I, X]), (5, [V]), (4, [I, V]), (1, [I])]

/-- `f` est une réserve de calcul. -/
def ecrire : Nat → List (Nat × List Chiffre) → Nat → List Chiffre
  | 0, _, _ => []
  | _, [], _ => []
  | f + 1, (v, s) :: r, n => if v ≤ n then s ++ ecrire f ((v, s) :: r) (n - v) else ecrire f r n

def romain (n : Nat) : List Chiffre := ecrire 30 briques n

def lire : List Chiffre → Nat -- @exo
  | [] => 0
  | [a] => a.val
  | a :: b :: r => if a.val < b.val then lire (b :: r) - a.val else a.val + lire (b :: r)

open Chiffre in
theorem exemples_romains : romain 2024 = [M, M, X, X, I, V] ∧ romain 1789 = [M, D, C, C, L, X, X, X, I, X] ∧
    lire [M, C, M, X, C] = 1990 := by -- @exo
  decide

theorem par_centaines : ∀ k, k < 40 → ∀ j, j < 100 → lire (romain (100 * k + j)) = 100 * k + j := by -- @exo
  decide +kernel

theorem aller_retour_romain (n : Nat) (h : n < 4000) : lire (romain n) = n := by -- @exo
  have := par_centaines (n / 100) (by omega) (n % 100) (Nat.mod_lt _ (by decide))
  rwa [Nat.div_add_mod] at this

end Parcours.Prog

#verifier
