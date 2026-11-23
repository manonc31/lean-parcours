import Exercices.Arithmetique.Definitions

/-!
# n⁵ − n est divisible par 30

Pour tout entier `n`, `n⁵ − n` est divisible par 2, par 3 et par 5, donc par 30.
La méthode des restes : `n⁵ mod 30` ne dépend que de `n mod 30`, et il n'y a que 30 restes à
essayer.

## À prouver
1. `puissance_cinq_mod : n ^ 5 % 30 = n % 30`
2. `cinq_trente : (n ^ 5 - n) % 30 = 0`

---
*Exercice* `Olympiades.CinqTrente` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Olympiades.CinqTrente` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Olymp

theorem puissance_cinq_mod (n : Nat) : n ^ 5 % 30 = n % 30 := by
  sorry

theorem cinq_trente (n : Nat) : (n ^ 5 - n) % 30 = 0 := by
  sorry

end Parcours.Olymp

#verifier
