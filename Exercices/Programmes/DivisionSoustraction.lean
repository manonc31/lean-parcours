import Exercices.Programmes.Definitions

/-!
# Diviser en soustrayant

Comment diviser quand on ne sait que soustraire ? On retire `b` de `a` tant qu'on peut, en
comptant les retraits : le nombre de retraits est le quotient, ce qui reste est le reste.

## À prouver
1. `divSous_spec : q * b + r = a ∧ r < b` où `(q, r) = divSous a b` (si `b > 0`)
2. `divSous_quotient : (divSous a b).1 = a / b`

---
*Exercice* `Programmes.DivisionSoustraction` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Programmes.DivisionSoustraction` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

def divSous (a b : Nat) : Nat × Nat :=
  if _ : 0 < b ∧ b ≤ a then ((divSous (a - b) b).1 + 1, (divSous (a - b) b).2) else (0, a)
termination_by a
decreasing_by omega

theorem divSous_spec (a b : Nat) (hb : 0 < b) :
    (divSous a b).1 * b + (divSous a b).2 = a ∧ (divSous a b).2 < b := by
  sorry

theorem divSous_quotient (a b : Nat) (hb : 0 < b) : (divSous a b).1 = a / b := by
  sorry

end Parcours.Prog

#verifier
