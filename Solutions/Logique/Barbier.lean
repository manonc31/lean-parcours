/- @parcours
titre: Le barbier de Russell
difficulte: 2
requiert: Logique.Negation
indice: Suppose qu'un tel barbier `b` existe : `rintro ⟨b, hb⟩`. Que dit `hb b` ?
indice: `hb b : rase b b ↔ ¬rase b b`. Montre d'abord `¬rase b b` (si `b` se rase, `hb b` dit qu'il ne se rase pas…).
indice: Puis `(hb b).mpr` appliqué à ce résultat donne `rase b b` : contradiction.
-/
import ParcoursOutils

/-!
# Le barbier de Russell

> Dans un village, le barbier rase **exactement** les hommes qui ne se rasent pas eux-mêmes.
> Qui rase le barbier ?

Un tel barbier ne peut pas exister. C'est la version « villageoise » du paradoxe de Russell
(l'ensemble des ensembles qui ne s'appartiennent pas), qui a ébranlé les fondements des
mathématiques en 1901… et qui explique pourquoi Lean a des **types**.

## À prouver
`barbier : ¬∃ b, ∀ x, rase b x ↔ ¬rase x x`

## Ressources
- [Paradoxe du barbier (Wikipédia)](https://fr.wikipedia.org/wiki/Paradoxe_du_barbier)
- [Paradoxe de Russell (Wikipédia)](https://fr.wikipedia.org/wiki/Paradoxe_de_Russell)
-/

namespace Parcours.Logique

theorem barbier {α : Type} (rase : α → α → Prop) : ¬∃ b, ∀ x, rase b x ↔ ¬rase x x := by -- @exo
  rintro ⟨b, hb⟩
  have h := hb b
  have hn : ¬rase b b := fun hr => (h.mp hr) hr
  exact hn (h.mpr hn)

end Parcours.Logique

#verifier
