/- @parcours
celebre: 38
titre: Moyenne arithmétique et géométrique
difficulte: 3
requiert: Olympiades.QuatreConsecutifs
indice: Sans perte de généralité `a ≤ b` (`Nat.le_total a b`). Écris alors `b = a + k` : `obtain ⟨k, rfl⟩ : ∃ k, b = a + k := ⟨b - a, by omega⟩`.
indice: Il reste `4 * a * (a + k) ≤ (a + (a + k)) ^ 2`, c'est-à-dire `0 ≤ k²` après développement : `grind`.
-/
import Solutions.Arithmetique.Definitions

/-!
# Moyenne arithmétique et géométrique

L'inégalité **arithmético-géométrique** : `√(ab) ≤ (a + b)/2`. Sans racine : `4ab ≤ (a + b)²`.
C'est l'inégalité la plus utilisée des olympiades. (Numéro 38 de la liste des « 100 théorèmes »,
dans sa version à deux nombres.)

## À prouver
`amgm (a b : Nat) : 4 * a * b ≤ (a + b) ^ 2`

## Ressources
- [Inégalité arithmético-géométrique (Wikipédia)](https://fr.wikipedia.org/wiki/In%C3%A9galit%C3%A9_arithm%C3%A9tico-g%C3%A9om%C3%A9trique)
-/

namespace Parcours.Olymp

theorem amgm (a b : Nat) : 4 * a * b ≤ (a + b) ^ 2 := by -- @exo
  rcases Nat.le_total a b with h | h
  · obtain ⟨k, rfl⟩ : ∃ k, b = a + k := ⟨b - a, by omega⟩
    grind
  · obtain ⟨k, rfl⟩ : ∃ k, a = b + k := ⟨a - b, by omega⟩
    grind

end Parcours.Olymp

#verifier
