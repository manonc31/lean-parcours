import Exercices.Listes.Pont
import Exercices.Recurrence.Definitions

/-!
# Missionnaires et cannibales

Trois missionnaires et trois cannibales doivent traverser une rivière avec une barque à deux
places. Si, sur une rive, les cannibales sont plus nombreux que les missionnaires (et qu'il y a
au moins un missionnaire), ça se passe mal. Comment faire ?

Un état `(m, c, b)` : nombre de missionnaires et de cannibales sur la rive de **départ**, et
`b = true` si la barque y est.

## À faire
1. Écris `solutionMC` et prouve `solutionMC_ok`.
2. `pas_moins_de_11` : impossible en moins de 11 traversées (l'ensemble des états atteints en au
   plus 10 traversées ne contient pas l'arrivée).

## Ressources
- [Problème des missionnaires et des cannibales (Wikipédia)](https://fr.wikipedia.org/wiki/Probl%C3%A8me_des_missionnaires_et_des_cannibales)

---
*Exercice* `Enigmes.Missionnaires` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Enigmes.Missionnaires` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Enigmes

abbrev Rive := Nat × Nat × Bool

def rivesSures (e : Rive) : Bool :=
  let (m, c, _) := e
  m ≤ 3 && c ≤ 3 && (m == 0 || c ≤ m) && (m == 3 || 3 - c ≤ 3 - m)

def apres (e : Rive) (p : Nat × Nat) : Option Rive :=
  let (m, c, b) := e
  if b then (if p.1 ≤ m && p.2 ≤ c then some (m - p.1, c - p.2, false) else none)
  else (if p.1 + m ≤ 3 && p.2 + c ≤ 3 then some (m + p.1, c + p.2, true) else none)

def voisinsMC (e : Rive) : List Rive :=
  ([(1, 0), (2, 0), (0, 1), (0, 2), (1, 1)].filterMap (apres e)).filter rivesSures

def cheminMC : List Rive → Bool
  | e :: e' :: r => (voisinsMC e).contains e' && cheminMC (e' :: r)
  | _ => true

def ValideMC (s : List Rive) : Bool :=
  s.head? == some (3, 3, true) && s.getLast? == some (0, 0, false) && cheminMC s

def solutionMC : List Rive :=
  sorry

theorem solutionMC_ok : ValideMC solutionMC = true := by
  sorry

/-- Les états atteints en au plus `k` traversées. -/
def atteints : Nat → List Rive
  | 0 => [(3, 3, true)]
  | k + 1 => ((atteints k).flatMap voisinsMC ++ atteints k).eraseDups

theorem pas_moins_de_11 : (atteints 10).contains (0, 0, false) = false := by
  sorry

end Parcours.Enigmes

#verifier
