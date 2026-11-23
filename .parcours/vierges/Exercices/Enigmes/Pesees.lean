import Exercices.Recurrence.Definitions

/-!
# Les quatre poids de Bachet

Avec seulement **quatre** poids de 1, 3, 9 et 27 kg, et une balance à deux plateaux, on peut
peser n'importe quelle masse entière de 1 à 40 kg ! (On a le droit de mettre des poids des deux
côtés.) C'est l'écriture des nombres en **base 3 équilibrée**, avec les chiffres −1, 0, 1.
Problème de Bachet de Méziriac (1612).

## À prouver
`bachet : (List.range 41).all (fun n => choix.any (fun t => pese t == n)) = true`

---
*Exercice* `Enigmes.Pesees` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Enigmes.Pesees` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Enigmes

/-- Les 81 façons de placer les 4 poids (−1, 0 ou +1 chacun). -/
def choix : List (Int × Int × Int × Int) :=
  [-1, 0, 1].flatMap fun a => [-1, 0, 1].flatMap fun b => [-1, 0, 1].flatMap fun c =>
    [-1, 0, 1].map fun d => (a, b, c, d)

def pese (t : Int × Int × Int × Int) : Int := t.1 + 3 * t.2.1 + 9 * t.2.2.1 + 27 * t.2.2.2

theorem bachet : (List.range 41).all (fun n => choix.any (fun t => pese t == (n : Int))) = true := by
  sorry

end Parcours.Enigmes

#verifier
