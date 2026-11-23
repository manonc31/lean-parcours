/- @parcours
titre: Le vol record de Syracuse
difficulte: 1
requiert: Programmes.FizzBuzz
indice: Des calculs : `decide` ou `decide +kernel`.
-/
import Solutions.Programmes.Definitions

/-!
# Le vol record de Syracuse

La suite de Syracuse (si `n` est pair, `n / 2`, sinon `3n + 1`) finit toujours par atteindre 1,
du moins pour tous les nombres qu'on a testés. Le « temps de vol » de 27 est spectaculaire :
111 étapes, en montant jusqu'à 9232, alors que ses voisins atterrissent en quelques étapes.

## À prouver
1. `vol_27` : 111 étapes et une altitude maximale de 9232.
2. `record_vol` : pourtant, sous 100, le record de durée est détenu par 97 (118 étapes) ;
3. `record_altitude` : et aucun nombre inférieur à 100 ne monte plus haut que 9232.

## Ressources
- [Conjecture de Syracuse (Wikipédia)](https://fr.wikipedia.org/wiki/Conjecture_de_Syracuse)
-/

namespace Parcours.Prog

def pasSyracuse (n : Nat) : Nat := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Nombre d'étapes pour atteindre 1 (`f` : réserve de calcul). -/
def vol : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, n => if n ≤ 1 then 0 else 1 + vol f (pasSyracuse n)

def altitude : Nat → Nat → Nat
  | 0, n => n
  | f + 1, n => if n ≤ 1 then n else max n (altitude f (pasSyracuse n))

theorem vol_27 : vol 200 27 = 111 ∧ altitude 200 27 = 9232 := by -- @exo
  decide +kernel

theorem record_vol : vol 200 97 = 118 ∧ ∀ n, n < 100 → vol 200 n ≤ vol 200 97 := by -- @exo
  decide +kernel

theorem record_altitude : ∀ n, n < 100 → altitude 200 n ≤ 9232 := by -- @exo
  decide +kernel

end Parcours.Prog

#verifier
