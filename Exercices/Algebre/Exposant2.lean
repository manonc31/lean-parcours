import Exercices.Algebre.Inverses

/-!
# Quand tout élément est son propre inverse

Si `x * x = 1` pour **tout** `x`, alors le groupe est **commutatif**. Joli, et surprenant !

## À prouver
`commutatif_si_carre_un (h : ∀ x : G, x * x = 1) (a b : G) : a * b = b * a`

---
*Exercice* `Algebre.Exposant2` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Algebre.Exposant2` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Algebre

variable {G : Type} [Groupe G]

theorem commutatif_si_carre_un (h : ∀ x : G, x * x = 1) (a b : G) : a * b = b * a := by
  sorry

end Parcours.Algebre

#verifier
