import Exercices.Algebre.Definitions

/-!
# Simplifier dans un groupe

Dans un groupe, on peut « simplifier » à gauche : si `a * b = a * c`, alors `b = c`.
(Faux dans `(ℕ, ×)` avec `a = 0` : ce n'est pas un groupe !)

## À prouver
1. `mul_gauche_simpl : a * b = a * c → b = c`
2. `idempotent : x * x = x → x = 1`

---
*Exercice* `Algebre.Simplification` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Algebre.Simplification` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Algebre

variable {G : Type} [Groupe G]

theorem mul_gauche_simpl {a b c : G} (h : a * b = a * c) : b = c := by
  sorry

theorem idempotent {x : G} (h : x * x = x) : x = 1 := by
  sorry

end Parcours.Algebre

#verifier
