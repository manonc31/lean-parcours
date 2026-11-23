/- @parcours
titre: Les tours du nombre pensé
difficulte: 1
requiert: Enigmes.PoulesLapins
indice: `omega` connaît la division par une constante.
-/
import Solutions.Recurrence.Definitions

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
-/

namespace Parcours.Enigmes

theorem toujours_cinq (n : Nat) : (2 * n + 10) / 2 - n = 5 := by -- @exo
  omega

theorem retour (n : Nat) : (3 * n + 6) / 3 - 2 = n := by -- @exo
  omega

theorem abcabc (n : Nat) (h : n < 1000) : (1000 * n + n) / 7 / 11 / 13 = n := by -- @exo
  omega

end Parcours.Enigmes

#verifier
