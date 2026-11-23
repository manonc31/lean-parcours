/- @parcours
titre: Remplacer une variable partout
difficulte: 2
requiert: Gymnase.Omega
indice: `subst h`, puis `omega`.
-/
import Solutions.Naturels.Transfert

/-!
# Remplacer une variable partout

`subst h` (avec `h : x = 5`) remplace `x` par `5` **partout** (but et hypothèses), et fait disparaître `x`.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem subst_exemple (x y : Nat) (h : x = 5) (h2 : x + y = 7) : y = 2 := by -- @exo
  subst h
  omega

end Parcours.Gymnase

#verifier
