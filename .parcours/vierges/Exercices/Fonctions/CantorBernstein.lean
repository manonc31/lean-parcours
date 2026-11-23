import Exercices.Fonctions.KnasterTarski
import Exercices.Fonctions.Images
import Exercices.Fonctions.Bijections

/-!
# 💀 Le théorème de Cantor–Schröder–Bernstein

> S'il existe une injection de `α` dans `β` et une injection de `β` dans `α`,
> alors il existe une **bijection** entre `α` et `β`.

Autrement dit : si `|α| ≤ |β|` et `|β| ≤ |α|` alors `|α| = |β|`, même pour des ensembles infinis.
Énoncé par Cantor (1887), prouvé par Bernstein et Schröder (1897), avec une longue histoire de preuves fausses.

Indication générale : la preuve via **Knaster–Tarski** (que tu as prouvé) est la plus courte.
Elle demande de bien manipuler images, complémentaires, et l'axiome du choix.

## À prouver
`cantor_schroeder_bernstein (f : α → β) (g : β → α) (hf : Injective f) (hg : Injective g) :
  ∃ h : α → β, Bijective h`

## Ressources
- [Théorème de Cantor-Bernstein (Wikipédia)](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_de_Cantor-Bernstein)

---
*Exercice* `Fonctions.CantorBernstein` · difficulté ★★★★★

💡 Indices : `./parcours indice Fonctions.CantorBernstein` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Fonctions

theorem cantor_schroeder_bernstein {α β : Type} (f : α → β) (g : β → α)
    (hf : Injective f) (hg : Injective g) : ∃ h : α → β, Bijective h := by
  sorry

end Parcours.Fonctions

#verifier
