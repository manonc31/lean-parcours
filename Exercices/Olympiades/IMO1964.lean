import Exercices.Arithmetique.Definitions

/-!
# IMO 1964, problème 1

> Trouver tous les entiers `n` tels que `2ⁿ − 1` est divisible par 7.

Réponse : exactement les multiples de 3. La suite des restes de `2ⁿ` modulo 7 est périodique :
`1, 2, 4, 1, 2, 4, …`

## À prouver
1. `reste_puissance_deux : 2 ^ n % 7 = (si n % 3 = 0 alors 1 sinon si n % 3 = 1 alors 2 sinon 4)`
2. `imo1964 (n : Nat) : (2 ^ n - 1) % 7 = 0 ↔ n % 3 = 0`

---
*Exercice* `Olympiades.IMO1964` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Olympiades.IMO1964` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Olymp

theorem reste_puissance_deux (n : Nat) :
    2 ^ n % 7 = if n % 3 = 0 then 1 else if n % 3 = 1 then 2 else 4 := by
  sorry

theorem imo1964 (n : Nat) : (2 ^ n - 1) % 7 = 0 ↔ n % 3 = 0 := by
  sorry

end Parcours.Olymp

#verifier
