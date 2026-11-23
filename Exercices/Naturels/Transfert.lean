import Exercices.Naturels.Pont

/-!
# Le transfert

Maintenant que le pont est construit, on peut faire **voyager** les théorèmes de `Nat` vers ton ℕ :
pour prouver une égalité dans ℕ, applique `toNat` des deux côtés (`toNat_injective`), pousse
`toNat` à l'intérieur (`toNat_add`, `toNat_mul`), et utilise la bibliothèque de `Nat`.

Comme cet exercice dépend du Pont, utiliser `Nat.add_comm` ou `omega` ici est **pur** ⭐.

## À prouver (sans récurrence !)
1. `add_comm_bis (a b : ℕ) : a + b = b + a`
2. `mul_comm_bis (a b : ℕ) : a * b = b * a`
3. `exemple_omega (a b : ℕ) : a + (b + a) + b = (a + a) + (b + b)`

---
*Exercice* `Naturels.Transfert` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Naturels.Transfert` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

theorem add_comm_bis (a b : ℕ) : a + b = b + a := by
  sorry

theorem mul_comm_bis (a b : ℕ) : a * b = b * a := by
  sorry

theorem exemple_omega (a b : ℕ) : a + (b + a) + b = (a + a) + (b + b) := by
  sorry

end Parcours.ℕ

#verifier
