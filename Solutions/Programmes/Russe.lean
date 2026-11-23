/- @parcours
titre: La multiplication russe
difficulte: 2
requiert: Programmes.Definitions
indice: `fun_induction russe a b` : trois cas (a = 0, a pair, a impair), avec l'hypothèse de récurrence pour `russe (a / 2) (2 * b)`.
indice: Écris `a = 2 * (a / 2)` (ou `+ 1`) grâce à `omega`, puis `generalize a / 2 = q` et `grind`.
-/
import Solutions.Programmes.Definitions

/-!
# La multiplication russe

La multiplication « du paysan russe » (ou égyptienne) : pour calculer `a × b`, on divise `a` par 2
et on double `b`, jusqu'à ce que `a` vaille 0 ; on additionne les `b` des lignes où `a` est
impair.

```
 13 × 7
  6 × 14   (pair : on barre)
  3 × 28
  1 × 56
 → 7 + 28 + 56 = 91
```
C'est exactement la multiplication en binaire, et la façon dont les processeurs multiplient.

## À prouver
`russe_spec : russe a b = a * b`

## Ressources
- [Multiplication égyptienne (Wikipédia)](https://fr.wikipedia.org/wiki/Technique_de_la_multiplication_%C3%A9gyptienne)
-/

namespace Parcours.Prog

def russe (a b : Nat) : Nat :=
  if a = 0 then 0
  else if a % 2 = 0 then russe (a / 2) (2 * b)
  else b + russe (a / 2) (2 * b)
termination_by a
decreasing_by all_goals omega

theorem russe_spec (a b : Nat) : russe a b = a * b := by -- @exo
  fun_induction russe a b with
  | case1 b => simp
  | case2 a b h1 h2 ih =>
    rw [ih]
    have e : a = 2 * (a / 2) := by omega
    conv => rhs; rw [e]
    generalize a / 2 = q
    grind
  | case3 a b h1 h2 ih =>
    rw [ih]
    have e : a = 2 * (a / 2) + 1 := by omega
    conv => rhs; rw [e]
    generalize a / 2 = q
    grind

end Parcours.Prog

#verifier
