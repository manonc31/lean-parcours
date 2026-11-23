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

---
*Exercice* `Logique.Barbier` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Logique.Barbier` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Logique

theorem barbier {α : Type} (rase : α → α → Prop) : ¬∃ b, ∀ x, rase b x ↔ ¬rase x x := by
  sorry

end Parcours.Logique

#verifier
