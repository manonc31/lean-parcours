import Exercices.Logique.Bilan

/-!
# Les involutions des booléens

Une fonction `f` est une **involution** si `f (f x) = x` pour tout `x` (la refaire annule son
effet, comme retourner une crêpe). Sur les booléens, il n'y en a que deux : l'identité et la
négation.

## À prouver
`involutions : (∀ b, f (f b) = b) → f = id ∨ f = not`

---
*Exercice* `Fonctions.InvolutionsBool` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Fonctions.InvolutionsBool` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Fonctions

theorem involutions (f : Bool → Bool) (h : ∀ b, f (f b) = b) : f = id ∨ f = not := by
  sorry

end Parcours.Fonctions

#verifier
