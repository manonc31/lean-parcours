import Exercices.Recurrence.Definitions

/-!
# Les sommes géométriques

`1 + 2 + 4 + ⋯ + 2ⁿ⁻¹ = 2ⁿ - 1` : c'est pour ça que le plus grand nombre sur `n` bits est `2ⁿ - 1`.
Plus généralement : `(r - 1)(1 + r + ⋯ + rⁿ⁻¹) = rⁿ - 1`.

Attention, dans `Nat`, `a - b = 0` quand `b > a` : on évite les soustractions en écrivant
« `+ 1` » de l'autre côté.

## À prouver
1. `somme_puissances_deux (n : Nat) : somme (fun i => 2 ^ i) n + 1 = 2 ^ n`
2. `somme_geometrique (r n : Nat) (hr : 1 ≤ r) : (r - 1) * somme (fun i => r ^ i) n + 1 = r ^ n`

## Ressources
- [Série géométrique (Wikipédia)](https://fr.wikipedia.org/wiki/S%C3%A9rie_g%C3%A9om%C3%A9trique)

---
*Exercice* `Recurrence.Geometrique` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Recurrence.Geometrique` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Recurrence

theorem somme_puissances_deux (n : Nat) : somme (fun i => 2 ^ i) n + 1 = 2 ^ n := by
  sorry

theorem somme_geometrique (r n : Nat) (hr : 1 ≤ r) :
    (r - 1) * somme (fun i => r ^ i) n + 1 = r ^ n := by
  sorry

end Parcours.Recurrence

#verifier
