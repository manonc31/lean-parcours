import Exercices.Listes.Pont
import Exercices.Recurrence.Definitions

/-!
# L'arithmétique de l'horloge

Sur une horloge, `9 h + 5 h = 2 h` : on calcule **modulo 12**. Dans ce monde, certains nombres ont
un inverse (`5 × 5 = 25 = 2 × 12 + 1`, donc `5⁻¹ = 5`), d'autres non (3, 4, 6…). Et il y a des
« diviseurs de zéro » : `3 × 4 = 0` ! Modulo un nombre premier comme 7, tout nombre non nul est
inversible : c'est un **corps**.

## À prouver
1. `neuf_plus_cinq`
2. `inversibles_douze : inversibles = [1, 5, 7, 11]` et chacun est son propre inverse.
3. `diviseurs_de_zero : 3 * 4 % 12 = 0`
4. `corps_sept` : modulo 7, tout `a ≠ 0` a un inverse.

## Ressources
- [Arithmétique modulaire (Wikipédia)](https://fr.wikipedia.org/wiki/Arithm%C3%A9tique_modulaire)

---
*Exercice* `Algebre.Horloge` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Algebre.Horloge` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Algebre

def inversibles : List Nat := (List.range 12).filter fun a => (List.range 12).any fun b => a * b % 12 == 1

theorem neuf_plus_cinq : (9 + 5) % 12 = 2 := by
  sorry

theorem inversibles_douze : inversibles = [1, 5, 7, 11] ∧ ∀ a ∈ inversibles, a * a % 12 = 1 := by
  sorry

theorem diviseurs_de_zero : 3 * 4 % 12 = 0 := by
  sorry

theorem corps_sept : ∀ a, a < 7 → 0 < a → ∃ b, b < 7 ∧ a * b % 7 = 1 := by
  sorry

end Parcours.Algebre

#verifier
