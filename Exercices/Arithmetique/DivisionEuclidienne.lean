import Exercices.Arithmetique.Definitions

/-!
# La division euclidienne

Pour `b > 0`, tout `a` s'écrit **de façon unique** `a = b·q + r` avec `0 ≤ r < b`.
C'est ce que calculent `a / b` (le quotient) et `a % b` (le reste)… mais ici tu dois le prouver
**sans** utiliser `/` ni `%` (le vérificateur refusera).

## À prouver
1. `division_euclidienne (a b : Nat) (hb : 0 < b) : ∃ q r, a = b * q + r ∧ r < b`
2. `unicite_division : a = b * q₁ + r₁ → a = b * q₂ + r₂ → r₁ < b → r₂ < b → q₁ = q₂ ∧ r₁ = r₂`

## Ressources
- [Division euclidienne (Wikipédia)](https://fr.wikipedia.org/wiki/Division_euclidienne)

---
*Exercice* `Arithmetique.DivisionEuclidienne` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Arithmetique.DivisionEuclidienne` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Arith

theorem division_euclidienne (a b : Nat) (hb : 0 < b) : ∃ q r, a = b * q + r ∧ r < b := by
  sorry

theorem unicite_division {a b q₁ r₁ q₂ r₂ : Nat} (h₁ : a = b * q₁ + r₁) (h₂ : a = b * q₂ + r₂)
    (hr₁ : r₁ < b) (hr₂ : r₂ < b) : q₁ = q₂ ∧ r₁ = r₂ := by
  sorry

end Parcours.Arith

#verifier
