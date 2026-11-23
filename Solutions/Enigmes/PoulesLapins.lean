/- @parcours
titre: Poules et lapins
difficulte: 1
requiert: Gymnase.Omega
indice: `omega` résout les systèmes d'équations linéaires sur les entiers.
-/
import Solutions.Recurrence.Definitions

/-!
# Poules et lapins

Un vieux problème chinois (Sunzi, IIIᵉ siècle) : dans une basse-cour, on compte 35 têtes et
94 pattes. Combien de poules, combien de lapins ?

## Se le représenter
Imagine que tous les animaux lèvent deux pattes : il reste `2 × 35 = 70` pattes au sol. Les
`94 − 70 = 24` pattes levées en trop appartiennent aux lapins, qui en lèvent 2 chacun :
`12` lapins, donc `23` poules.

## À prouver
`poules_lapins : p + l = 35 → 2 * p + 4 * l = 94 → p = 23 ∧ l = 12`
-/

namespace Parcours.Enigmes

theorem poules_lapins (p l : Nat) (htetes : p + l = 35) (hpattes : 2 * p + 4 * l = 94) :
    p = 23 ∧ l = 12 := by -- @exo
  omega

end Parcours.Enigmes

#verifier
