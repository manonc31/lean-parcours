/- @parcours
titre: Le complément à un
difficulte: 3
indice: Récurrence sur `l`. Pour `b :: l`, `(!b).toNat + b.toNat = 1` (`cases b <;> rfl`).
indice: Avec `ih`, `List.length_cons` et `Nat.pow_succ`, `omega` conclut.
-/
import Solutions.Circuits.Definitions

/-!
# Le complément à un

Inverser tous les bits d'un nombre de `n` bits donne `(2ⁿ − 1) − x`. C'est la base du
« complément à deux », la façon dont les processeurs représentent les nombres négatifs
(`-x = complément(x) + 1`).

## À prouver
`complement : valeur (l.map (!·)) + valeur l + 1 = 2 ^ l.length`
-/

namespace Parcours.Circuits

theorem complement (l : List Bool) : valeur (l.map (!·)) + valeur l + 1 = 2 ^ l.length := by -- @exo
  induction l with
  | nil => rfl
  | cons b l ih =>
    have hb : (!b).toNat + b.toNat = 1 := by cases b <;> rfl
    simp only [List.map_cons, valeur_cons, List.length_cons, Nat.pow_succ]
    omega

end Parcours.Circuits

#verifier
