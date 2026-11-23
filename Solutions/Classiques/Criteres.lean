/- @parcours
titre: Les critères de divisibilité
difficulte: 1
requiert: Classiques.NeufEtDix
indice: `omega` connaît `%` par une constante.
-/
import Solutions.Recurrence.Definitions
import Solutions.Listes.Pont

/-!
# Les critères de divisibilité

## Se le représenter
Pourquoi suffit-il de regarder le dernier chiffre pour savoir si un nombre est divisible par 2
ou 5 ? Parce que `n = 10 × (n / 10) + (dernier chiffre)` et que 10 est divisible par 2 et 5.
Même idée avec les deux derniers chiffres pour 4 et 25 (`100 = 4 × 25`), et les trois derniers pour 8.

## À prouver
1. `par_deux : n % 2 = (n % 10) % 2` (et pareil pour 5)
2. `par_quatre : n % 4 = (n % 100) % 4` (et pareil pour 25)
3. `par_huit : n % 8 = (n % 1000) % 8`
-/

namespace Parcours.Classiques

theorem par_deux (n : Nat) : n % 2 = (n % 10) % 2 ∧ n % 5 = (n % 10) % 5 := by -- @exo
  omega

theorem par_quatre (n : Nat) : n % 4 = (n % 100) % 4 ∧ n % 25 = (n % 100) % 25 := by -- @exo
  omega

theorem par_huit (n : Nat) : n % 8 = (n % 1000) % 8 := by -- @exo
  omega

end Parcours.Classiques

#verifier
