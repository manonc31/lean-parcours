/- @parcours
titre: Les partitions d'un entier
difficulte: 2
requiert: Combinatoire.UnEuro
indice: Des calculs : `decide` / `decide +kernel`.
-/
import Solutions.Combinatoire.Definitions

/-!
# Les partitions d'un entier

De combien de façons peut-on écrire 5 comme somme d'entiers, sans tenir compte de l'ordre ?
`5 = 4+1 = 3+2 = 3+1+1 = 2+2+1 = 2+1+1+1 = 1+1+1+1+1` : 7 façons. C'est `p(5)`. Cette suite
grandit très vite : `p(10) = 42`, `p(100) = 190 569 292`. Ramanujan et Hardy ont trouvé une formule
asymptotique étonnante, et Ramanujan a remarqué que `p(5k + 4)` est toujours divisible par 5 !

## À prouver
1. `p_cinq`, `p_dix`, `p_vingt`
2. `ramanujan` : `p(4)`, `p(9)`, `p(14)`, `p(19)`, `p(24)` sont divisibles par 5.

## Ressources
- [Partition d'un entier (Wikipédia)](https://fr.wikipedia.org/wiki/Partition_d%27un_entier)
-/

namespace Parcours.Combi

/-- Nombre de partitions de `n` en parts au plus égales à `k` (`f` : réserve). -/
def partAux : Nat → Nat → Nat → Nat
  | _, 0, _ => 1
  | _, _, 0 => 0
  | 0, _, _ => 0
  | f + 1, n + 1, k + 1 =>
    partAux f (n + 1) k + (if k + 1 ≤ n + 1 then partAux f (n + 1 - (k + 1)) (k + 1) else 0)

def nbPartitions (n : Nat) : Nat := partAux (2 * n + 1) n n

theorem p_cinq : nbPartitions 5 = 7 := by -- @exo
  decide

theorem p_dix : nbPartitions 10 = 42 := by -- @exo
  decide +kernel

theorem p_vingt : nbPartitions 20 = 627 := by -- @exo
  decide +kernel

theorem ramanujan : ∀ k, k < 5 → nbPartitions (5 * k + 4) % 5 = 0 := by -- @exo
  decide +kernel

end Parcours.Combi

#verifier
