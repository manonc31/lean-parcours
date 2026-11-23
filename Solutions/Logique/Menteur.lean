/- @parcours
titre: Le paradoxe du menteur
difficulte: 1
requiert: Logique.Equivalence
indice: Montre d'abord `¬P` : si `P`, alors `¬P` (par `h.mp`), contradiction.
indice: Puis `h.mpr` donne `P`.
-/
import ParcoursOutils

/-!
# Le paradoxe du menteur

Épiménide le Crétois dit : « Tous les Crétois sont menteurs. » Version plus radicale : « Cette
phrase est fausse. » Si elle est vraie, elle est fausse ; si elle est fausse, elle est vraie. En
logique, aucune proposition ne peut être équivalente à sa propre négation.

## À prouver
`menteur : ¬ (P ↔ ¬P)`
-/

namespace Parcours.Logique

theorem menteur (P : Prop) : ¬ (P ↔ ¬P) := by -- @exo
  intro h
  have hnp : ¬P := fun hp => h.mp hp hp
  exact hnp (h.mpr hnp)

end Parcours.Logique

#verifier
