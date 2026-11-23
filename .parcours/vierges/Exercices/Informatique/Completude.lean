import Exercices.Informatique.LogiqueProp

/-!
# 💀 Le théorème de complétude

La réciproque de la correction : **toute tautologie est prouvable** dans le système à la Hilbert.
Avec la correction, cela dit que « vrai » et « prouvable » coïncident en logique propositionnelle.
(Gödel montrera que c'est encore vrai en logique du premier ordre… mais pas pour l'arithmétique !)

Boss sans solution de référence.

## À prouver
`completude (f : Formule) (h : ∀ v, f.eval v = true) : Prouvable f`

## Ressources
- [Théorème de complétude (Wikipédia)](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_de_compl%C3%A9tude_de_G%C3%B6del)

---
*Exercice* `Informatique.Completude` · difficulté ★★★★★

💡 Indices : `./parcours indice Informatique.Completude` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Info

theorem completude (f : Formule) (h : ∀ v, f.eval v = true) : Prouvable f := by
  sorry

end Parcours.Info

#verifier
