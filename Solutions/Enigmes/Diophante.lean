/- @parcours
titre: L'épitaphe de Diophante
difficulte: 2
requiert: Gymnase.Omega
indice: `omega` sait gérer les divisions par des constantes !
indice: À la main : écris `x = 84k` ; l'équation devient `75k + 9 = 84k`.
-/
import Solutions.Recurrence.Definitions

/-!
# L'épitaphe de Diophante

« Passant, sous ce tombeau repose Diophante. Ces quelques vers vont te dire la durée de sa vie.
Son enfance en a occupé la sixième partie ; puis sa barbe a poussé pendant un douzième ; il se maria
après un septième, et cinq ans plus tard il eut un fils. Mais ce fils mourut à la moitié de l'âge
qu'atteignit son père, qui lui survécut quatre ans. »

En notant `x` l'âge de Diophante (multiple de 84 pour que toutes les fractions soient entières) :
`x/6 + x/12 + x/7 + 5 + x/2 + 4 = x`.

## À prouver
`diophante (h84 : x % 84 = 0) (h : x / 6 + x / 12 + x / 7 + 5 + x / 2 + 4 = x) : x = 84`
-/

namespace Parcours.Enigmes

theorem diophante (x : Nat) (h84 : x % 84 = 0) (h : x / 6 + x / 12 + x / 7 + 5 + x / 2 + 4 = x) :
    x = 84 := by -- @exo
  omega

end Parcours.Enigmes

#verifier
