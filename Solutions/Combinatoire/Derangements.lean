/- @parcours
titre: Le problème des chapeaux
difficulte: 2
requiert: Combinatoire.Anagrammes
indice: Ce sont des calculs : `decide +kernel`.
indice: Essaie `#eval derangements 3` pour voir les 2 dérangements de 3 objets.
-/
import Solutions.Combinatoire.Anagrammes

/-!
# Le problème des chapeaux

`n` personnes déposent leur chapeau au vestiaire ; on les leur rend au hasard. Quelle est la
probabilité que **personne** ne récupère le sien ? Ce sont les **dérangements** (permutations sans
point fixe). Leur nombre vérifie `D(n + 2) = (n + 1)(D(n) + D(n + 1))`, et la probabilité tend vers
`1/e ≈ 0,3679` (Montmort, 1708) — presque indépendamment de `n` !

## À prouver
1. `quatre_cinq` : en comptant pour de vrai, `D(4) = 9` et `D(5) = 44`.
2. `recurrence_ok` : la formule de récurrence donne les bons nombres pour `n ≤ 5`.
3. `un_sur_e` : pour 10 personnes, la probabilité est `0,367…`

## Ressources
- [Dérangement (Wikipédia)](https://fr.wikipedia.org/wiki/D%C3%A9rangement)
-/

namespace Parcours.Combi

open Parcours.Recurrence

def derangements (n : Nat) : List (List Nat) :=
  (perms (List.range n)).filter fun p => (List.range n).all fun i => p.getD i 0 != i

def der : Nat → Nat
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1) * (der n + der (n + 1))

theorem quatre_cinq : (derangements 4).length = 9 ∧ (derangements 5).length = 44 := by -- @exo
  decide +kernel

theorem recurrence_ok : ∀ n, n < 6 → (derangements n).length = der n := by -- @exo
  decide +kernel

theorem un_sur_e : der 10 * 1000 / fact 10 = 367 := by -- @exo
  decide

end Parcours.Combi

#verifier
