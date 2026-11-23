/- @parcours
titre: Combien de carrés sur un échiquier ?
difficulte: 3
requiert: Recurrence.Carres
indice: Récurrence ; `simp only [carres]`, puis `grind`.
indice: Pour l'échiquier : `decide`.
-/
import Solutions.Recurrence.Definitions

/-!
# Combien de carrés sur un échiquier ?

## Se le représenter
Sur un échiquier `n × n`, combien de carrés de toutes tailles ? Pour la taille `k`, il y en a
`(n − k + 1)²`. Au total : `1² + 2² + ⋯ + n²`. Pour un échiquier 8 × 8 : 204 carrés ! On définit
`carres (n + 1) = carres n + (n + 1)²` (agrandir la grille d'un rang ajoute `(n+1)²` carrés).

## À prouver
`carres_grille (n : Nat) : 6 * carres n = n * (n + 1) * (2 * n + 1)`, et `carres 8 = 204`
-/

namespace Parcours.Classiques

open Parcours.Recurrence

def carres : Nat → Nat
  | 0 => 0
  | n + 1 => carres n + (n + 1) ^ 2

theorem carres_grille (n : Nat) : 6 * carres n = n * (n + 1) * (2 * n + 1) := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [carres]
    grind

theorem echiquier : carres 8 = 204 := by -- @exo
  decide

end Parcours.Classiques

#verifier
