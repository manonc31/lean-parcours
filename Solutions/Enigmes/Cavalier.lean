/- @parcours
titre: Le tour du cavalier
difficulte: 2
requiert: Enigmes.Echiquier
indice: **Règle de Warnsdorff** : va toujours vers la case qui a le moins de sorties encore libres.
indice: Commence par le coin 0 ; les cases voisines du coin sont 7 et 11.
-/
import Solutions.Listes.Pont
import Solutions.Recurrence.Definitions

/-!
# Le tour du cavalier

Un cavalier d'échecs peut-il visiter **toutes** les cases d'un échiquier, chacune une seule fois ?
Euler s'y est intéressé en 1759. Sur un échiquier 5 × 5, c'est possible en partant d'un coin.
Sur un 3 × 3, c'est impossible : la case centrale est inaccessible !

Les cases d'un échiquier `n × n` sont numérotées de `0` à `n² − 1` (ligne par ligne).

## À faire
1. Écris `tour5` (un tour du cavalier sur l'échiquier 5 × 5) et prouve `tour5_ok`.
2. `centre_isole` : sur l'échiquier 3 × 3, aucun saut ne mène à la case centrale (4).

## Ressources
- [Problème du cavalier (Wikipédia)](https://fr.wikipedia.org/wiki/Probl%C3%A8me_du_cavalier)
-/

namespace Parcours.Enigmes

def saut (n a b : Nat) : Bool :=
  let x := a / n
  let y := a % n
  let x' := b / n
  let y' := b % n
  ((x + 1 == x' || x' + 1 == x) && (y + 2 == y' || y' + 2 == y)) ||
    ((x + 2 == x' || x' + 2 == x) && (y + 1 == y' || y' + 1 == y))

def sauts (n : Nat) : List Nat → Bool
  | a :: b :: r => saut n a b && sauts n (b :: r)
  | _ => true

def TourCavalier (n : Nat) (l : List Nat) : Bool :=
  l.length == n * n && l.all (· < n * n) && l.eraseDups.length == n * n && sauts n l

def tour5 : List Nat := -- @exo
  [0, 7, 4, 13, 24, 17, 20, 11, 18, 9, 2, 5, 16, 23, 14, 3, 6, 15, 22, 19, 8, 1, 12, 21, 10]

theorem tour5_ok : TourCavalier 5 tour5 = true := by -- @exo
  decide

theorem centre_isole : ∀ b, b < 9 → saut 3 b 4 = false := by -- @exo
  decide

end Parcours.Enigmes

#verifier
