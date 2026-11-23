/- @parcours
titre: La récurrence fonctionnelle
difficulte: 3
requiert: Gymnase.RecurrenceNat
indice: `fun_induction pas2 n with`, trois cas : `case1`, `case2`, `case3 n ih`.
indice: Dans le dernier cas, le but est `pas2 n + 2 = n + 2` : `omega` avec `ih`.
-/
import Solutions.Naturels.Transfert

/-!
# La récurrence fonctionnelle

Pour une fonction récursive qui ne suit pas un schéma simple, `fun_induction f n with` fait une récurrence qui **suit les appels récursifs** de `f`. Ici `pas2` descend de 2 en 2.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

def pas2 : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => pas2 n + 2

theorem pas2_eq (n : Nat) : pas2 n = n := by -- @exo
  fun_induction pas2 n with
  | case1 => rfl
  | case2 => rfl
  | case3 n ih => omega

end Parcours.Gymnase

#verifier
