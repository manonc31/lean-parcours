import Exercices.Naturels.PowMul

/-!
# L'identité remarquable

`(a + b)² = a² + 2ab + b²`. Au collège, c'est une ligne. Ici, c'est le boss final
de l'arithmétique de Peano : il faut tout ce que tu as prouvé jusqu'ici.

🔑 **Récompense** : cet exercice débloque le jeton **`anneau`**. Dans les exercices qui en
dépendent, tu pourras utiliser la tactique `grind`, qui sait faire ce genre de calcul
toute seule (et bien plus). Tu as prouvé que tu savais le faire à la main !

## À prouver
`carre_somme (a b : ℕ) : (a + b) ^ (2 : ℕ) = a ^ (2 : ℕ) + 2 * a * b + b ^ (2 : ℕ)`

---
*Exercice* `Naturels.Carre` · difficulté ★★★★☆

💡 Indices : `./parcours indice Naturels.Carre` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

theorem carre_somme (a b : ℕ) : (a + b) ^ (2 : ℕ) = a ^ (2 : ℕ) + 2 * a * b + b ^ (2 : ℕ) := by
  sorry

end Parcours.ℕ

#verifier
