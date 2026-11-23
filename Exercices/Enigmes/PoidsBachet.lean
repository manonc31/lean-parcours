import Exercices.Listes.Pont
import Exercices.Recurrence.Definitions

/-!
# Les poids de Bachet

Avec seulement 4 poids, de 1, 3, 9 et 27 grammes, on peut peser **toutes** les masses entières
de 1 à 40 grammes, à condition de pouvoir poser des poids sur **les deux** plateaux de la balance
(Bachet de Méziriac, 1624). Avec un seul plateau, il faut les puissances de 2 : 1, 2, 4, 8, 16, 32
permettent de peser de 0 à 63.

## À prouver
1. `bachet_quarante` : tout `n ≤ 40` est pesable avec 1, 3, 9, 27 (deux plateaux).
2. `binaire_63` : tout `n < 64` est pesable avec 1, 2, 4, 8, 16, 32 (un plateau).

## Ressources
- [Problème des poids de Bachet (Wikipédia)](https://fr.wikipedia.org/wiki/Probl%C3%A8me_des_poids_de_Bachet)

---
*Exercice* `Enigmes.PoidsBachet` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Enigmes.PoidsBachet` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Enigmes

/-- Les masses pesables : chaque poids est à gauche (`−`), absent, ou à droite (`+`). -/
def pesables : List Nat → List Int
  | [] => [0]
  | p :: ps => (pesables ps).flatMap fun m => [m - p, m, m + p]

/-- Les masses pesables avec un seul plateau. -/
def sommes : List Nat → List Nat
  | [] => [0]
  | p :: ps => (sommes ps).flatMap fun m => [m, m + p]

theorem bachet_quarante : ∀ n : Nat, n < 41 → (n : Int) ∈ pesables [1, 3, 9, 27] := by
  sorry

theorem binaire_63 : ∀ n, n < 64 → n ∈ sommes [1, 2, 4, 8, 16, 32] := by
  sorry

end Parcours.Enigmes

#verifier
