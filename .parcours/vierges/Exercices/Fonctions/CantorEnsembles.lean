import Exercices.Fonctions.Definitions
import Exercices.Logique.Cantor

/-!
# Cantor, version ensembles

Tu as prouvé le théorème de Cantor dans la branche Logique. Ce fichier **l'importe** :
réutilise-le pour montrer qu'aucune fonction `α → Ens α` n'est surjective.

## À prouver
`cantor_ens (f : α → Ens α) : ¬Surjective f`

---
*Exercice* `Fonctions.CantorEnsembles` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Fonctions.CantorEnsembles` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Fonctions

theorem cantor_ens {α : Type} (f : α → Ens α) : ¬Surjective f := by
  sorry

end Parcours.Fonctions

#verifier
