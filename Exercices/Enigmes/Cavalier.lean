import Exercices.Listes.Pont
import Exercices.Recurrence.Definitions

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

---
*Exercice* `Enigmes.Cavalier` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Enigmes.Cavalier` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
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

def tour5 : List Nat :=
  sorry

theorem tour5_ok : TourCavalier 5 tour5 = true := by
  sorry

theorem centre_isole : ∀ b, b < 9 → saut 3 b 4 = false := by
  sorry

end Parcours.Enigmes

#verifier
