import Exercices.Naturels.SuccAdd

/-!
# Commutativité de l'addition

Le grand classique : `a + b = b + a`. Dans la bibliothèque de Lean c'est une ligne
(`Nat.add_comm`)… mais ici, c'est **ton** ℕ, et il n'y a que **tes** théorèmes.

## À prouver
`add_comm (a b : ℕ) : a + b = b + a`

## Tes outils
`add_zero`, `add_succ`, `zero_add`, `succ_add`.

---
*Exercice* `Naturels.AddComm` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Naturels.AddComm` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

theorem add_comm (a b : ℕ) : a + b = b + a := by
  sorry

end Parcours.ℕ

#verifier
