/- @parcours
titre: Donnant-donnant
difficulte: 2
requiert: Jeux.Nash
indice: Tout est calcul : `decide`.
indice: Essaie `#eval partie donnant rancunier 10 [] []` pour explorer.
-/
import Solutions.Listes.Pont
import Solutions.Recurrence.Definitions

/-!
# Donnant-donnant

Le **dilemme du prisonnier répété** : à chaque tour, deux joueurs choisissent de coopérer
(`true`) ou de trahir (`false`). Gains : 3 chacun si les deux coopèrent, 1 chacun si les deux
trahissent, et 5 pour le traître contre 0 pour la victime.

En 1980, Robert Axelrod organisa un tournoi de programmes. Le vainqueur fut le plus simple :
**donnant-donnant** (coopérer au premier tour, puis copier le dernier coup de l'adversaire).
Paradoxe : le méchant (qui trahit toujours) ne perd **aucun** duel… mais finit dernier du tournoi !

## À prouver (sur des parties de 10 tours)
1. `duel : partie donnant mechant 10 [] [] = (9, 14)`
2. `mechant_invaincu` : le méchant gagne ou fait match nul contre chacun.
3. `tournoi` : les scores totaux sont 90 (gentil), 88 (méchant), 99 (donnant), 99 (rancunier).

## Ressources
- [Dilemme du prisonnier (Wikipédia)](https://fr.wikipedia.org/wiki/Dilemme_du_prisonnier)
- [The Evolution of Trust (jeu interactif)](https://ncase.me/trust/)
-/

namespace Parcours.Jeux

/-- Une stratégie décide selon les coups passés de l'adversaire (le plus récent en tête). -/
abbrev Strategie := List Bool → Bool

def gentil : Strategie := fun _ => true
def mechant : Strategie := fun _ => false
def donnant : Strategie := fun h => h.headD true
def rancunier : Strategie := fun h => h.all id

def gainPD : Bool → Bool → Nat
  | true, true => 3
  | true, false => 0
  | false, true => 5
  | false, false => 1

/-- Scores de `s` et `t` après `n` tours (`hs`, `ht` : coups déjà joués par chacun). -/
def partie (s t : Strategie) : Nat → List Bool → List Bool → Nat × Nat
  | 0, _, _ => (0, 0)
  | n + 1, hs, ht =>
    let a := s ht
    let b := t hs
    let r := partie s t n (a :: hs) (b :: ht)
    (gainPD a b + r.1, gainPD b a + r.2)

def joueurs : List Strategie := [gentil, mechant, donnant, rancunier]

def total (s : Strategie) : Nat := (joueurs.map fun t => (partie s t 10 [] []).1).sum

theorem duel : partie donnant mechant 10 [] [] = (9, 14) := by -- @exo
  decide

theorem mechant_invaincu : ∀ t ∈ joueurs, (partie mechant t 10 [] []).2 ≤ (partie mechant t 10 [] []).1 := by -- @exo
  decide

theorem tournoi : joueurs.map total = [90, 88, 99, 99] := by -- @exo
  decide

end Parcours.Jeux

#verifier
