import Exercices.Programmes.Definitions

/-!
# Deux façons de sommer les pairs

Deux programmes pour additionner les nombres pairs d'une liste : avec une boucle et un `if`,
ou en **filtrant** d'abord puis en sommant. Ils calculent la même chose — prouvons-le.

## À prouver
`deux_versions : sommePairsBoucle l = (l.filter (· % 2 == 0)).sum`

---
*Exercice* `Programmes.SommePairs` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Programmes.SommePairs` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

def sommePairsBoucle : List Nat → Nat
  | [] => 0
  | x :: l => (if x % 2 = 0 then x else 0) + sommePairsBoucle l

theorem deux_versions (l : List Nat) : sommePairsBoucle l = (l.filter (· % 2 == 0)).sum := by
  sorry

end Parcours.Prog

#verifier
