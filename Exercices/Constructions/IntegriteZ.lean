import Exercices.Constructions.PontZ

/-!
# ℤ est intègre (grâce au pont)

Un produit nul a un facteur nul. Plutôt que de le prouver sur les couples (pénible), on
**transporte** le résultat de `Int` via le pont. C'est toute la puissance des isomorphismes.

## À prouver
`mul_eq_zero (x y : Zr) : x * y = 0 → x = 0 ∨ y = 0`

---
*Exercice* `Constructions.IntegriteZ` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Constructions.IntegriteZ` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Constructions

theorem Zr.mul_eq_zero (x y : Zr) (h : x * y = 0) : x = 0 ∨ y = 0 := by
  sorry

end Parcours.Constructions

#verifier
