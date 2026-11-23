import ParcoursOutils

/-!
# Pas de plus petit que zéro

Contre-exemple à « pour tout `n`, il existe `m < n` » : prends `n = 0` ! En Lean, `m < 0` est
impossible, et `cases` le voit (aucune règle ne permet de construire une preuve de `m < 0`).

## À prouver
`pas_de_plus_petit : ¬∀ n : Nat, ∃ m, m < n`

---
*Exercice* `Logique.PasDePlusPetit` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Logique.PasDePlusPetit` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Logique

theorem pas_de_plus_petit : ¬∀ n : Nat, ∃ m, m < n := by
  sorry

end Parcours.Logique

#verifier
