import Exercices.Programmes.Definitions

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

---
*Exercice* `Programmes.Russe` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Programmes.Russe` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

def russe (a b : Nat) : Nat :=
  if a = 0 then 0
  else if a % 2 = 0 then russe (a / 2) (2 * b)
  else b + russe (a / 2) (2 * b)
termination_by a
decreasing_by all_goals omega

theorem russe_spec (a b : Nat) : russe a b = a * b := by
  sorry

end Parcours.Prog

#verifier
