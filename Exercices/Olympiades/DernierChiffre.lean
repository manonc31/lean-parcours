import Exercices.Arithmetique.Definitions

/-!
# Le dernier chiffre de 7²⁰²⁵

Quel est le dernier chiffre de `7²⁰²⁵` (un nombre de 1712 chiffres) ? Les derniers chiffres des
puissances de 7 forment un cycle : `7, 9, 3, 1, 7, 9, 3, 1…` (car `7⁴ = 2401` finit par 1).
Comme `2025 = 4 × 506 + 1`, c'est **7**.

## À prouver
1. `sept_cycle : 7 ^ (4 * k + 1) % 10 = 7`
2. `dernier_chiffre : 7 ^ 2025 % 10 = 7` (sans calculer `7²⁰²⁵` !)

---
*Exercice* `Olympiades.DernierChiffre` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Olympiades.DernierChiffre` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Olymp

theorem sept_cycle (k : Nat) : 7 ^ (4 * k + 1) % 10 = 7 := by
  sorry

theorem dernier_chiffre : 7 ^ 2025 % 10 = 7 := by
  sorry

end Parcours.Olymp

#verifier
