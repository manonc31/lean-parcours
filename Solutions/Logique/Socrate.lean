/- @parcours
titre: Le syllogisme de Socrate
difficulte: 1
requiert: Logique.PourTout
indice: `h1 socrate h2` : on applique « pour tout x » à Socrate.
indice: Pour la contraposée : `intro h`, puis il faut prouver `False`.
-/
import ParcoursOutils

/-!
# Le syllogisme de Socrate

« Tous les hommes sont mortels. Socrate est un homme. Donc Socrate est mortel. » C'est le
**syllogisme** le plus célèbre (Aristote). En Lean, « tous les hommes sont mortels » est une
fonction qui, à tout `x` et toute preuve que `x` est un homme, associe une preuve que `x` est
mortel.

## À prouver
1. `socrate`
2. `contraposee_zeus` : si Zeus n'est pas mortel, Zeus n'est pas un homme.
-/

namespace Parcours.Logique

theorem socrate {Etre : Type} (Homme Mortel : Etre → Prop) (socrate : Etre)
    (h1 : ∀ x, Homme x → Mortel x) (h2 : Homme socrate) : Mortel socrate := by -- @exo
  exact h1 socrate h2

theorem contraposee_zeus {Etre : Type} (Homme Mortel : Etre → Prop) (zeus : Etre)
    (h1 : ∀ x, Homme x → Mortel x) (h2 : ¬Mortel zeus) : ¬Homme zeus := by -- @exo
  intro h
  exact h2 (h1 zeus h)

end Parcours.Logique

#verifier
