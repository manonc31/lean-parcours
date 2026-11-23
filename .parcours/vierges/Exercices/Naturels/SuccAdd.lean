import Exercices.Naturels.ZeroAdd

/-!
# Successeur à gauche

Par définition, `a + succ b = succ (a + b)`. Prouve la version « à gauche ».

## À prouver
`succ_add (a b : ℕ) : succ a + b = succ (a + b)`

---
*Exercice* `Naturels.SuccAdd` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Naturels.SuccAdd` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

theorem succ_add (a b : ℕ) : succ a + b = succ (a + b) := by
  sorry

end Parcours.ℕ

#verifier
