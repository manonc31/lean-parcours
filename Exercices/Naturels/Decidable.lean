import Exercices.Naturels.Strict

/-!
# Un algorithme pour ≤

Jusqu'ici, `a ≤ b` est une **proposition** (`∃ c, b = a + c`) : on ne peut pas « calculer »
si elle est vraie. Écris une **fonction** `ble : ℕ → ℕ → Bool` qui répond `true` ou `false`,
puis **prouve** qu'elle donne toujours la bonne réponse.

C'est ton premier exercice « algorithme + preuve » : tu dois écrire la définition (remplace
le `sorry` de `ble`), puis prouver sa correction. Tu peux tester ta fonction avec
`#eval ble 3 5`.

Une fois prouvé, on en déduit une instance `Decidable (a ≤ b)` : la tactique `decide`
saura désormais vérifier des inégalités !

## À faire
1. `def ble : ℕ → ℕ → Bool` (à programmer, par récurrence)
2. `ble_correct (a b : ℕ) : ble a b = true ↔ a ≤ b`

---
*Exercice* `Naturels.Decidable` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Naturels.Decidable` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

def ble : ℕ → ℕ → Bool :=
  sorry

theorem ble_correct (a b : ℕ) : ble a b = true ↔ a ≤ b := by
  sorry

instance (a b : ℕ) : Decidable (a ≤ b) :=
  decidable_of_iff (ble a b = true) (ble_correct a b)

end Parcours.ℕ

#verifier
