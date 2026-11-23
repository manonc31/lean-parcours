/- @parcours
titre: n² + n + 1 n'est pas un carré
difficulte: 2
requiert: Olympiades.EntreDeuxCarres
indice: Deux cas : `k ≤ n` ou `k ≥ n + 1` (`Nat.lt_or_ge`).
indice: `Nat.mul_le_mul : a ≤ b → c ≤ d → a * c ≤ b * d`. Puis `omega` (il traite `k * k` et `n * n` comme des inconnues).
-/
import Solutions.Arithmetique.Definitions

/-!
# n² + n + 1 n'est pas un carré

Pour `n ≥ 1`, `n² + n + 1` est coincé strictement entre deux carrés consécutifs :
`n² < n² + n + 1 < (n + 1)² = n² + 2n + 1`. Donc ce n'est pas un carré.

## À prouver
`pas_un_carre : 1 ≤ n → k * k ≠ n * n + n + 1`
-/

namespace Parcours.Olymp

theorem pas_un_carre (n k : Nat) (hn : 1 ≤ n) : k * k ≠ n * n + n + 1 := by -- @exo
  intro h
  rcases Nat.lt_or_ge n k with hk | hk
  · have h1 : (n + 1) * (n + 1) ≤ k * k := Nat.mul_le_mul hk hk
    have e : (n + 1) * (n + 1) = n * n + 2 * n + 1 := by grind
    omega
  · have : k * k ≤ n * n := Nat.mul_le_mul hk hk
    omega

end Parcours.Olymp

#verifier
