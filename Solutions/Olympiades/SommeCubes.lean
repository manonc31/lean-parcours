/- @parcours
titre: Somme de trois cubes
difficulte: 2
requiert: Olympiades.QuatreConsecutifs
indice: Exprime `c` en fonction de `a` et `b` (`omega`), puis `subst`.
indice: Il reste une identité polynomiale : `grind`.
-/
import Solutions.Arithmetique.Definitions

/-!
# Somme de trois cubes

Si `a + b + c = 0`, alors `a³ + b³ + c³ = 3abc`. Une identité qui sert souvent en compétition
(par exemple pour factoriser).

## À prouver
`somme_cubes (a b c : Int) (h : a + b + c = 0) : a ^ 3 + b ^ 3 + c ^ 3 = 3 * a * b * c`
-/

namespace Parcours.Olymp

theorem somme_cubes (a b c : Int) (h : a + b + c = 0) : a ^ 3 + b ^ 3 + c ^ 3 = 3 * a * b * c := by -- @exo
  have hc : c = -a - b := by omega
  subst hc
  grind

end Parcours.Olymp

#verifier
