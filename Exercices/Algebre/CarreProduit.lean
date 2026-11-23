import Exercices.Algebre.Inverses

/-!
# Le carré d'un produit

Dans un groupe, `(ab)² = a²b²` si et seulement si `a` et `b` **commutent**. (Dans un groupe non
commutatif, l'identité `(ab)² = a²b²` est donc fausse en général !)

## À prouver
`carre_produit : a * b * (a * b) = a * a * (b * b) ↔ a * b = b * a`

---
*Exercice* `Algebre.CarreProduit` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Algebre.CarreProduit` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Algebre

variable {G : Type} [Groupe G]

theorem carre_produit (a b : G) : a * b * (a * b) = a * a * (b * b) ↔ a * b = b * a := by
  sorry

end Parcours.Algebre

#verifier
