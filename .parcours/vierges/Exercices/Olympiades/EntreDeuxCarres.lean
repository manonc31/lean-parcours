import Exercices.Arithmetique.Definitions

/-!
# Rien entre deux carrés consécutifs

Il n'y a aucun carré parfait strictement entre `n²` et `(n + 1)²`.

## À prouver
`entre_deux_carres : ¬∃ m, n * n < m * m ∧ m * m < (n + 1) * (n + 1)`

---
*Exercice* `Olympiades.EntreDeuxCarres` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Olympiades.EntreDeuxCarres` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Olymp

theorem entre_deux_carres (n : Nat) : ¬∃ m, n * n < m * m ∧ m * m < (n + 1) * (n + 1) := by
  sorry

end Parcours.Olymp

#verifier
