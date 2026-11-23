import Exercices.Programmes.Definitions

/-!
# Mastermind

Au Mastermind, un joueur cache une combinaison de 4 couleurs (parmi 6) ; l'autre propose des
combinaisons et reçoit deux indices : le nombre de pions **bien placés**, et le nombre de pions
de la bonne couleur mais **mal placés**.

## À prouver
1. `exemple_mastermind` : pour le secret `[1, 2, 3, 4]` et la proposition `[1, 3, 2, 5]` : 1 bien placé, 2 mal placés.
2. `bienPlaces_le` : il y a au plus autant de bien placés que de pions.
3. `bienPlaces_comm` : l'indice « bien placés » est symétrique.

## Ressources
- [Mastermind (Wikipédia)](https://fr.wikipedia.org/wiki/Mastermind)

---
*Exercice* `Programmes.Mastermind` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Programmes.Mastermind` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

def bienPlaces (s g : List Nat) : Nat := (List.zipWith (· == ·) s g).count true

def communs (s g : List Nat) : Nat := ((List.range 6).map fun c => min (s.count c) (g.count c)).sum

def malPlaces (s g : List Nat) : Nat := communs s g - bienPlaces s g

theorem exemple_mastermind : bienPlaces [1, 2, 3, 4] [1, 3, 2, 5] = 1 ∧ malPlaces [1, 2, 3, 4] [1, 3, 2, 5] = 2 := by
  sorry

theorem bienPlaces_le (s g : List Nat) : bienPlaces s g ≤ s.length := by
  sorry

theorem bienPlaces_comm (s g : List Nat) : bienPlaces s g = bienPlaces g s := by
  sorry

end Parcours.Prog

#verifier
