import Exercices.Listes.Pont
import Exercices.Recurrence.Definitions

/-!
# Le tour des 21 cartes

Un tour de magie classique (déjà décrit par Gergonne en 1813) : le magicien distribue 21 cartes
en trois tas, le spectateur indique le tas qui contient sa carte, et le magicien ramasse les tas en
mettant celui-là **au milieu**. Après trois distributions, la carte choisie est toujours la
**onzième** !

## Se le représenter
Si la carte est en position `p` (de 0 à 20), elle se retrouve dans le tas `p % 3` en position
`p / 3`, et après ramassage en position `7 + p / 3`. Partant de `p ≤ 20` : après un tour,
`7 ≤ p ≤ 13` ; après deux, `9 ≤ p ≤ 11` ; après trois, `p = 10`.

## À prouver
1. `onzieme` : la simulation avec de vraies listes.
2. `position` : le calcul sur les positions.

## Ressources
- [Tour de cartes de Gergonne (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Gergonne%27s_three_pile_problem)

---
*Exercice* `Enigmes.VingtEtUnCartes` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Enigmes.VingtEtUnCartes` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Enigmes

/-- Distribue les cartes une par une sur trois tas. -/
def distribuer {α : Type} : List α → List α × List α × List α
  | a :: b :: c :: r =>
    let t := distribuer r
    (a :: t.1, b :: t.2.1, c :: t.2.2)
  | [a, b] => ([a], [b], [])
  | [a] => ([a], [], [])
  | [] => ([], [], [])

/-- Ramasse les tas en mettant au milieu celui qui contient la carte `c`. -/
def ramasser (c : Nat) (t : List Nat × List Nat × List Nat) : List Nat :=
  if t.1.contains c then t.2.1 ++ t.1 ++ t.2.2
  else if t.2.1.contains c then t.1 ++ t.2.1 ++ t.2.2
  else t.1 ++ t.2.2 ++ t.2.1

def unTour (c : Nat) (paquet : List Nat) : List Nat := ramasser c (distribuer paquet)

theorem onzieme : ∀ c, c < 21 → (unTour c (unTour c (unTour c (List.range 21)))).idxOf c = 10 := by
  sorry

theorem position (p : Nat) (h : p < 21) : 7 + (7 + (7 + p / 3) / 3) / 3 = 10 := by
  sorry

end Parcours.Enigmes

#verifier
