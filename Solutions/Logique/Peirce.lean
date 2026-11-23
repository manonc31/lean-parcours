/- @parcours
titre: La loi de Peirce
difficulte: 3
indice: Raisonne par cas sur `P` avec `Classical.em P`.
indice: Si `P` est faux, `h` attend une preuve de `P → Q` : donne-lui `fun hp => absurd hp hnp`.
-/
import Solutions.Logique.Classique

/-!
# La loi de Peirce

`((P → Q) → P) → P` : une formule qui ne contient que des implications, et pourtant
elle n'est vraie qu'en logique **classique**. Charles Sanders Peirce l'a découverte en 1885.

## À prouver
`peirce : ((P → Q) → P) → P`

## Ressources
- [Loi de Peirce (Wikipédia)](https://fr.wikipedia.org/wiki/Loi_de_Peirce)
-/

namespace Parcours.Logique

variable {P Q : Prop}

theorem peirce : ((P → Q) → P) → P := by -- @exo
  intro h
  rcases Classical.em P with hp | hnp
  · exact hp
  · exact h (fun hp => absurd hp hnp)

end Parcours.Logique

#verifier
