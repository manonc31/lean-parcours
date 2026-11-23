import Exercices.Arithmetique.Definitions

/-!
# Deux carrés qui diffèrent de 2

Deux carrés parfaits ne diffèrent **jamais** de 2. L'astuce : regarder modulo 4. Un carré vaut
toujours 0 ou 1 modulo 4.

## À prouver
`difference_carres : ¬∃ x y : Nat, x * x = y * y + 2`

---
*Exercice* `Olympiades.DifferenceCarres` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Olympiades.DifferenceCarres` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Olymp

theorem difference_carres : ¬∃ x y : Nat, x * x = y * y + 2 := by
  sorry

end Parcours.Olymp

#verifier
