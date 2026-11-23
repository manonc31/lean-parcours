/- @parcours
titre: Le taquin de Sam Loyd
difficulte: 2
requiert: Enigmes.Missionnaires
indice: Ce sont des explorations exhaustives : `decide +kernel`.
indice: Pour comprendre l'invariant : chaque coup échange le trou avec une pièce ; la parité de la permutation change à chaque coup, et la parité de la position du trou aussi.
-/
import Solutions.Listes.Pont
import Solutions.Recurrence.Definitions

/-!
# Le taquin de Sam Loyd

En 1880, le taquin (15 pièces glissantes dans un cadre 4 × 4) rend l'Amérique folle. Sam Loyd
promet 1000 dollars à qui remettra dans l'ordre une grille où seules les pièces 14 et 15 sont
échangées. Personne ne gagne : c'est **impossible**, pour une raison de parité.

On joue ici sur un petit taquin 2 × 3 (5 pièces et un trou). Il y a `6! = 720` configurations,
mais seule la **moitié** est atteignable depuis la position rangée.

Un état est codé par un nombre en base 6 : le chiffre `i` est la pièce de la case `i` (0 = trou),
les cases étant numérotées
```
0 1 2
3 4 5
```

## À prouver
1. `moitie` : exactement 360 configurations sont atteignables.
2. `loyd` : la position rangée avec les pièces 1 et 2 échangées ne l'est pas.

## Ressources
- [Taquin (Wikipédia)](https://fr.wikipedia.org/wiki/Taquin)
-/

namespace Parcours.Enigmes

def chiffre (e i : Nat) : Nat := e / 6 ^ i % 6

def echanger (e i j : Nat) : Nat :=
  e - chiffre e i * 6 ^ i - chiffre e j * 6 ^ j + chiffre e j * 6 ^ i + chiffre e i * 6 ^ j

def voisinsCase : Nat → List Nat
  | 0 => [1, 3] | 1 => [0, 2, 4] | 2 => [1, 5] | 3 => [0, 4] | 4 => [1, 3, 5] | 5 => [2, 4]
  | _ => []

def trou (e : Nat) : Nat := ((List.range 6).find? (chiffre e · == 0)).getD 0

def coups (e : Nat) : List Nat := (voisinsCase (trou e)).map (echanger e (trou e))

/-- Parcours en largeur : `vus` = déjà atteints, `front` = atteints à la dernière étape. -/
def explorer : Nat → List Nat → List Nat → List Nat
  | 0, vus, _ => vus
  | f + 1, vus, front =>
    let nouveaux := ((front.flatMap coups).eraseDups).filter (fun e => !vus.contains e)
    if nouveaux.isEmpty then vus else explorer f (vus ++ nouveaux) nouveaux

/-- `1 2 3 / 4 5 _` -/
def range : Nat := 1 + 2 * 6 + 3 * 6 ^ 2 + 4 * 6 ^ 3 + 5 * 6 ^ 4

/-- `2 1 3 / 4 5 _` -/
def loydPos : Nat := 2 + 1 * 6 + 3 * 6 ^ 2 + 4 * 6 ^ 3 + 5 * 6 ^ 4

theorem moitie : (explorer 30 [range] [range]).length = 360 := by -- @exo
  decide +kernel

theorem loyd : (explorer 30 [range] [range]).contains loydPos = false := by -- @exo
  decide +kernel

end Parcours.Enigmes

#verifier
