/- @parcours
titre: Le tour du 1089
difficulte: 1
requiert: Enigmes.PoulesLapins
indice: Calcul sur les 1000 nombres : `decide +kernel`.
indice: Pour comprendre : avec les chiffres `a > c`, la différence vaut `99 (a − c)`, donc ses chiffres sont `a − c − 1`, `9`, `10 − (a − c)`.
-/
import Solutions.Recurrence.Definitions

/-!
# Le tour du 1089

Un tour de magie : pense à un nombre de 3 chiffres dont le premier chiffre est plus grand que le
dernier (par exemple 732). Retourne-le (237) et soustrais : `732 − 237 = 495`. Retourne le
résultat (594) et ajoute : `495 + 594 = 1089`. Quel que soit ton nombre, tu trouves **1089** !

(Les nombres comme 99 s'écrivent 099 sur trois chiffres.)

## À prouver
`tour_1089 : n < 1000 → n % 10 < n / 100 → tour1089 n = 1089`
-/

namespace Parcours.Enigmes

def renverser3 (n : Nat) : Nat := (n % 10) * 100 + (n / 10 % 10) * 10 + n / 100

def tour1089 (n : Nat) : Nat := (n - renverser3 n) + renverser3 (n - renverser3 n)

theorem tour_1089 : ∀ n, n < 1000 → n % 10 < n / 100 → tour1089 n = 1089 := by -- @exo
  decide +kernel

end Parcours.Enigmes

#verifier
