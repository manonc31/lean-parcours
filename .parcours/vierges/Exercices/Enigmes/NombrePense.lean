import Exercices.Recurrence.Definitions

/-!
# Les tours du nombre pensé

« Pense à un nombre. Multiplie-le par 2, ajoute 10, divise par 2, et retire le nombre de
départ : tu trouves 5 ! » Le magicien n'a aucun mérite : c'est une identité algébrique.

Autre tour : « Écris un nombre de 3 chiffres deux fois de suite (`abcabc`), divise par 7, puis
par 11, puis par 13 : tu retrouves ton nombre ! » Car `abcabc = 1001 × abc` et `1001 = 7 × 11 × 13`.

## À prouver
1. `toujours_cinq : (2 * n + 10) / 2 - n = 5`
2. `retour : (3 * n + 6) / 3 - 2 = n`
3. `abcabc : n < 1000 → (1000 * n + n) / 7 / 11 / 13 = n`

---
*Exercice* `Enigmes.NombrePense` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Enigmes.NombrePense` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Enigmes

theorem toujours_cinq (n : Nat) : (2 * n + 10) / 2 - n = 5 := by
  sorry

theorem retour (n : Nat) : (3 * n + 6) / 3 - 2 = n := by
  sorry

theorem abcabc (n : Nat) (h : n < 1000) : (1000 * n + n) / 7 / 11 / 13 = n := by
  sorry

end Parcours.Enigmes

#verifier
