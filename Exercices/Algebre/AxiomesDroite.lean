import Exercices.Algebre.Simplification

/-!
# Les axiomes à droite

On a seulement supposé `1 * a = a` et `a⁻¹ * a = 1`. Montre que l'on a aussi, gratuitement :
`a * a⁻¹ = 1` et `a * 1 = a`. C'est un grand classique (et un petit casse-tête).

## À prouver
1. `mul_inv (a : G) : a * a⁻¹ = 1`
2. `mul_one (a : G) : a * 1 = a`

---
*Exercice* `Algebre.AxiomesDroite` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Algebre.AxiomesDroite` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Algebre

variable {G : Type} [Groupe G]

theorem mul_inv (a : G) : a * a⁻¹ = 1 := by
  sorry

theorem mul_one (a : G) : a * 1 = a := by
  sorry

end Parcours.Algebre

#verifier
