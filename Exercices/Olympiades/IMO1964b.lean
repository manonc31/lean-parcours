import Exercices.Olympiades.IMO1964

/-!
# IMO 1964, problème 1 (b)

> Montrer qu'il n'existe aucun entier `n` tel que `2ⁿ + 1` soit divisible par 7.

Les restes de `2ⁿ` modulo 7 sont `1, 2, 4` : en ajoutant 1, on obtient `2, 3, 5`, jamais 0.

## À prouver
`imo1964b : (2 ^ n + 1) % 7 ≠ 0`

---
*Exercice* `Olympiades.IMO1964b` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Olympiades.IMO1964b` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Olymp

theorem imo1964b (n : Nat) : (2 ^ n + 1) % 7 ≠ 0 := by
  sorry

end Parcours.Olymp

#verifier
