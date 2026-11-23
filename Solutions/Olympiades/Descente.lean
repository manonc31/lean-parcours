/- @parcours
titre: La descente infinie
difficulte: 4
requiert: Olympiades.TroisCarres
indice: Récurrence forte sur `z` : `induction z using Nat.strongRecOn`.
indice: Avec `trois_divise_carres`, écris `x = 3a`, `y = 3b` (`obtain ⟨a, rfl⟩ : ∃ a, x = 3 * a := ⟨x / 3, by omega⟩`). Puis montre que `3` divise `z`, et écris `z = 3c`.
indice: On obtient `a² + b² = 3c²` avec `c < z` (si `c ≠ 0`) : l'hypothèse de récurrence dit `c = 0`, contradiction. Et si `c = 0`, tout est nul.
-/
import Solutions.Olympiades.TroisCarres

/-!
# La descente infinie

L'équation `x² + y² = 3z²` n'a que la solution `x = y = z = 0`.

## Se le représenter
C'est la **descente infinie** de Fermat : si `(x, y, z)` est une solution, alors 3 divise `x` et `y`
(exercice précédent), donc `9` divise `3z²`, donc 3 divise `z`, et `(x/3, y/3, z/3)` est une solution
**plus petite**. On ne peut pas descendre indéfiniment dans les entiers naturels : il faut que tout
soit nul.

En Lean, la descente infinie est une **récurrence forte** sur `z`.

## À prouver
`descente : x * x + y * y = 3 * (z * z) → x = 0 ∧ y = 0 ∧ z = 0`

## Ressources
- [Descente infinie (Wikipédia)](https://fr.wikipedia.org/wiki/Descente_infinie)
-/

namespace Parcours.Olymp

theorem descente : ∀ z x y : Nat, x * x + y * y = 3 * (z * z) → x = 0 ∧ y = 0 ∧ z = 0 := by -- @exo
  intro z
  induction z using Nat.strongRecOn with
  | ind z ih =>
    intro x y h
    obtain ⟨hx, hy⟩ := trois_divise_carres x y (by omega)
    obtain ⟨a, rfl⟩ : ∃ a, x = 3 * a := ⟨x / 3, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, y = 3 * b := ⟨y / 3, by omega⟩
    have e1 : 3 * a * (3 * a) + 3 * b * (3 * b) = 9 * (a * a + b * b) := by grind
    have hz : z % 3 = 0 := by
      have : (z * z) % 3 = 0 := by omega
      have hz3 : z % 3 = 0 ∨ z % 3 = 1 ∨ z % 3 = 2 := by omega
      rcases hz3 with h3 | h3 | h3 <;> simp [Nat.mul_mod, h3] at this ⊢
    obtain ⟨c, rfl⟩ : ∃ c, z = 3 * c := ⟨z / 3, by omega⟩
    have e2 : 3 * c * (3 * c) = 9 * (c * c) := by grind
    have h' : a * a + b * b = 3 * (c * c) := by omega
    by_cases hc : c = 0
    · subst hc
      have ha : a * a = 0 := by omega
      have hb : b * b = 0 := by omega
      have ha' : a = 0 := (Nat.mul_eq_zero.mp ha).elim id id
      have hb' : b = 0 := (Nat.mul_eq_zero.mp hb).elim id id
      subst ha' hb'
      simp
    · have := ih c (by omega) a b h'
      omega

end Parcours.Olymp

#verifier
