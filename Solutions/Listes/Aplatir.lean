/- @parcours
titre: Aplatir une liste de listes
difficulte: 3
requiert: Listes.Plis
indice: Récurrence sur `ll` ; dans le cas `cons`, `show` déplie les définitions.
indice: `longueur_concat` puis l'hypothèse de récurrence.
-/
import Solutions.Listes.Plis
import Solutions.Listes.Longueur

/-!
# Aplatir une liste de listes

`aplatir [[1, 2], [], [3]] = [1, 2, 3]`. Sa longueur est la somme des longueurs.

## À prouver
`longueur_aplatir : longueur (aplatir ll) = somme (map longueur ll)`
-/

namespace Parcours.Listes.Liste

def aplatir {α : Type} : Liste (Liste α) → Liste α
  | nil => nil
  | l ∷ ll => l ++ aplatir ll

theorem longueur_aplatir {α : Type} (ll : Liste (Liste α)) :
    longueur (aplatir ll) = somme (map longueur ll) := by -- @exo
  induction ll with
  | nil => rfl
  | cons l ll ih =>
    show longueur (l ++ aplatir ll) = longueur l + somme (map longueur ll)
    rw [longueur_concat, ih]

end Parcours.Listes.Liste

#verifier
