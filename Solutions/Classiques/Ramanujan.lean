/- @parcours
titre: Le taxi de Ramanujan
difficulte: 1
requiert: Classiques.Pythagore
indice: `decide` / `decide +kernel`.
-/
import Solutions.Listes.Pont
import Solutions.Recurrence.Definitions

/-!
# Le taxi de Ramanujan

Le mathématicien Hardy rend visite à Ramanujan à l'hôpital, en taxi n°1729 : « un nombre plutôt
ennuyeux ». Ramanujan répond aussitôt : « Non, c'est un nombre très intéressant : c'est le plus
petit nombre qui s'écrit de deux façons différentes comme somme de deux cubes ! »
`1729 = 1³ + 12³ = 9³ + 10³`.

## À prouver
1. `deux_facons`
2. `plus_petit` : les sommes de deux cubes plus petites que 1729 sont toutes différentes (pour
   `n < 1729`, les cubes utiles sont au plus `12³ = 1728`).

## Ressources
- [1729 (nombre) (Wikipédia)](https://fr.wikipedia.org/wiki/1729_(nombre))
-/

namespace Parcours.Classiques

/-- Toutes les sommes `a³ + b³` avec `a ≤ b ≤ 12`. -/
def sommesCubes : List Nat :=
  (List.range 13).flatMap fun a => ((List.range 13).filter fun b => a ≤ b).map fun b => a ^ 3 + b ^ 3

theorem deux_facons : 1729 = 1 ^ 3 + 12 ^ 3 ∧ 1729 = 9 ^ 3 + 10 ^ 3 ∧ sommesCubes.count 1729 = 2 := by -- @exo
  decide

theorem plus_petit : (sommesCubes.filter (· < 1729)).Nodup := by -- @exo
  decide +kernel

end Parcours.Classiques

#verifier
