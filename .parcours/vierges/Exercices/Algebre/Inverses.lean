import Exercices.Algebre.Unicite

/-!
# Calculs avec les inverses

« Pour défaire une action composée, on défait les actions dans l'ordre inverse » :
pour enlever chaussettes puis chaussures, on enlève d'abord les chaussures !

## À prouver
1. `inv_inv : (a⁻¹)⁻¹ = a`
2. `inv_one : (1 : G)⁻¹ = 1`
3. `mul_inv_rev : (a * b)⁻¹ = b⁻¹ * a⁻¹`

---
*Exercice* `Algebre.Inverses` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Algebre.Inverses` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Algebre

variable {G : Type} [Groupe G]

theorem inv_inv (a : G) : (a⁻¹)⁻¹ = a := by
  sorry

theorem inv_one : (1 : G)⁻¹ = 1 := by
  sorry

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  sorry

end Parcours.Algebre

#verifier
