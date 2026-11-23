import Exercices.Arithmetique.Definitions

/-!
# Onze divise 10²ⁿ⁺¹ + 1

`11`, `1001 = 7 × 11 × 13`, `100001 = 11 × 9091`… Les nombres `10^(2n+1) + 1` sont tous divisibles par 11.
(Critère de divisibilité par 11 : `10 ≡ −1` modulo 11.)

## À prouver
`onze (n : Nat) : (10 ^ (2 * n + 1) + 1) % 11 = 0`

---
*Exercice* `Olympiades.Onze` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Olympiades.Onze` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Olymp

theorem onze (n : Nat) : (10 ^ (2 * n + 1) + 1) % 11 = 0 := by
  sorry

end Parcours.Olymp

#verifier
