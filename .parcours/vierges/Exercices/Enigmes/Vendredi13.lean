import Exercices.Listes.Pont
import Exercices.Recurrence.Definitions

/-!
# Il y a un vendredi 13 chaque année

Chaque année, il y a au moins un vendredi 13, et au plus trois. Pourquoi ? Le jour de la
semaine du 13 de chaque mois ne dépend que du jour de la semaine du 13 janvier et de l'année
(bissextile ou non) ; et les 12 mois couvrent forcément les 7 jours de la semaine.

Les jours sont numérotés `0` (lundi) à `6` (dimanche) : vendredi = 4.

## À prouver
1. `au_moins_un : ∀ d < 7, ∀ b, 4 ∈ treizes d b`
2. `au_plus_trois : ∀ d < 7, ∀ b, (treizes d b).count 4 ≤ 3`

---
*Exercice* `Enigmes.Vendredi13` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Enigmes.Vendredi13` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Enigmes

def longueursMois (bissextile : Bool) : List Nat :=
  [31, if bissextile then 29 else 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]

/-- Le jour de la semaine du 13 de chaque mois, si le 13 janvier tombe le jour `d`. -/
def treizes (d : Nat) (b : Bool) : List Nat :=
  (List.range 12).map fun k => (d + ((longueursMois b).take k).sum) % 7

theorem au_moins_un : ∀ d, d < 7 → ∀ b : Bool, 4 ∈ treizes d b := by
  sorry

theorem au_plus_trois : ∀ d, d < 7 → ∀ b : Bool, (treizes d b).count 4 ≤ 3 := by
  sorry

end Parcours.Enigmes

#verifier
