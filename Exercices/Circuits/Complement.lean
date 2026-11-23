import Exercices.Circuits.Definitions

/-!
# Le complément à un

Inverser tous les bits d'un nombre de `n` bits donne `(2ⁿ − 1) − x`. C'est la base du
« complément à deux », la façon dont les processeurs représentent les nombres négatifs
(`-x = complément(x) + 1`).

## À prouver
`complement : valeur (l.map (!·)) + valeur l + 1 = 2 ^ l.length`

---
*Exercice* `Circuits.Complement` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Circuits.Complement` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Circuits

theorem complement (l : List Bool) : valeur (l.map (!·)) + valeur l + 1 = 2 ^ l.length := by
  sorry

end Parcours.Circuits

#verifier
