import Exercices.Algebre.AxiomesDroite

/-!
# Unicité du neutre et de l'inverse

Il n'y a qu'un seul élément neutre, et chaque élément n'a qu'un seul inverse. C'est pour ça
qu'on peut dire « **le** neutre » et « **l'**inverse ».

## À prouver
1. `neutre_unique : (∀ a, e * a = a) → e = 1`
2. `inverse_unique : a * b = 1 → b = a⁻¹`

---
*Exercice* `Algebre.Unicite` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Algebre.Unicite` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Algebre

variable {G : Type} [Groupe G]

theorem neutre_unique {e : G} (h : ∀ a, e * a = a) : e = 1 := by
  sorry

theorem inverse_unique {a b : G} (h : a * b = 1) : b = a⁻¹ := by
  sorry

end Parcours.Algebre

#verifier
