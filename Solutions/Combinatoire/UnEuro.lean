/- @parcours
titre: Combien de façons de payer 1 € ?
difficulte: 2
requiert: Combinatoire.Menus
indice: Des calculs : `decide +kernel`.
indice: La réserve de calcul `f` sert à garantir que le programme s'arrête (chaque appel la fait baisser).
-/
import Solutions.Combinatoire.Definitions

/-!
# Combien de façons de payer 1 € ?

Avec des pièces de 1, 2, 5, 10, 20 et 50 centimes, combien de façons de faire exactement 1 € ?
Il y en a **4562** ! On compte avec une récurrence : les façons de payer `n` avec les pièces
`p :: ps` sont celles qui n'utilisent pas `p`, plus celles qui en utilisent au moins une.

## À prouver
1. `facons_un_euro : facons 100 [1, 2, 5, 10, 20, 50] = 4562`
2. `pieces_1_2 : facons n [1, 2] = n / 2 + 1` (avec des 1 et des 2, on choisit juste le nombre de 2)

## Ressources
- [Projet Euler, problème 31 (les pièces anglaises)](https://projecteuler.net/problem=31)
-/

namespace Parcours.Combi

/-- Nombre de façons de payer `n` avec les pièces de la liste (`f` : réserve de calcul). -/
def faconsAux : Nat → Nat → List Nat → Nat
  | _, 0, _ => 1
  | _, _, [] => 0
  | 0, _, _ => 0
  | f + 1, n + 1, p :: ps => faconsAux f (n + 1) ps + (if p ≤ n + 1 ∧ 0 < p then faconsAux f (n + 1 - p) (p :: ps) else 0)

def facons (n : Nat) (pieces : List Nat) : Nat := faconsAux (2 * n + pieces.length + 1) n pieces

theorem facons_un_euro : facons 100 [1, 2, 5, 10, 20, 50] = 4562 := by -- @exo
  decide +kernel

theorem pieces_1_2 : ∀ n, n < 50 → facons n [1, 2] = n / 2 + 1 := by -- @exo
  decide +kernel

end Parcours.Combi

#verifier
