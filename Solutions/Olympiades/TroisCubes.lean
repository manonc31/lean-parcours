/- @parcours
titre: Trois cubes consécutifs
difficulte: 2
requiert: Classiques.Divisible3
indice: Réutilise `Parcours.Classiques.divisible_trois`, et écris `n³ + 2n = 3k`.
indice: Puis montre `n³ + (n+1)³ + (n+2)³ = 9(k + n + n² + 1)` avec `grind`.
-/
import Solutions.Classiques.Divisible3

/-!
# Trois cubes consécutifs

La somme de trois cubes consécutifs est toujours divisible par 9 : `1 + 8 + 27 = 36`,
`8 + 27 + 64 = 99`, `27 + 64 + 125 = 216`…

## Se le représenter
En développant : `n³ + (n+1)³ + (n+2)³ = 3(n³ + 2n) + 9(n² + n + 1)`. Et tu sais déjà que
`n³ + 2n` est divisible par 3 !

## À prouver
`trois_cubes : (n ^ 3 + (n + 1) ^ 3 + (n + 2) ^ 3) % 9 = 0`
-/

namespace Parcours.Olymp

theorem trois_cubes (n : Nat) : (n ^ 3 + (n + 1) ^ 3 + (n + 2) ^ 3) % 9 = 0 := by -- @exo
  have h := Parcours.Classiques.divisible_trois n
  obtain ⟨k, hk⟩ : ∃ k, n * n * n + 2 * n = 3 * k := ⟨(n * n * n + 2 * n) / 3, by omega⟩
  have e : n ^ 3 + (n + 1) ^ 3 + (n + 2) ^ 3 = 9 * (k + n + n * n + 1) := by grind
  rw [e]
  omega

end Parcours.Olymp

#verifier
