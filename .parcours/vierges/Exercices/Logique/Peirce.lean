import Exercices.Logique.Classique

/-!
# La loi de Peirce

`((P → Q) → P) → P` : une formule qui ne contient que des implications, et pourtant
elle n'est vraie qu'en logique **classique**. Charles Sanders Peirce l'a découverte en 1885.

## À prouver
`peirce : ((P → Q) → P) → P`

## Ressources
- [Loi de Peirce (Wikipédia)](https://fr.wikipedia.org/wiki/Loi_de_Peirce)

---
*Exercice* `Logique.Peirce` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Logique.Peirce` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Logique

variable {P Q : Prop}

theorem peirce : ((P → Q) → P) → P := by
  sorry

end Parcours.Logique

#verifier
