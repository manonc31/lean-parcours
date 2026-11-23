import Exercices.Constructions.CorpsQ
import Exercices.Recurrence.Definitions
import Exercices.Listes.Pont

/-!
# Suites et limites (cours)

On travaille avec les rationnels de Lean, `Rat` (débloqués depuis que tu as construit ℚ).
`grind` sait raisonner sur les inégalités **linéaires** entre rationnels (comme `omega` sur `Nat`).

## Définitions
- `vabs x` : la valeur absolue (`-x` si `x < 0`, sinon `x`).
- Une **suite** est une fonction `u : Nat → Rat`.
- `Tend u l` (« `u` tend vers `l` ») : pour tout `ε > 0`, il existe un rang `N` à partir duquel
  `|u n - l| < ε`. C'est **la** définition de Cauchy et Weierstrass (XIXᵉ siècle).
- `Cauchy u` : les termes finissent par être arbitrairement proches **les uns des autres**.

## Outils donnés
- `archimede ε hε : ∃ N, 1 / (N + 1) < ε` (propriété d'Archimède, prouvée ici).
- Pour la valeur absolue : `unfold vabs` puis `split` (deux cas) puis `grind`.
- Le rang « à partir duquel deux propriétés sont vraies » : `max N N'` (`omega` connaît `max`).

## Ressources
- [Limite d'une suite (Wikipédia)](https://fr.wikipedia.org/wiki/Limite_d%27une_suite)
- [Suite de Cauchy (Wikipédia)](https://fr.wikipedia.org/wiki/Suite_de_Cauchy)

---
*Exercice* `Analyse.Definitions` · difficulté ★☆☆☆☆
-/

namespace Parcours.Analyse

/-- La valeur absolue d'un rationnel. -/
def vabs (x : Rat) : Rat := if x < 0 then -x else x

abbrev Suite := Nat → Rat

/-- `u` tend vers `l`. -/
def Tend (u : Suite) (l : Rat) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → vabs (u n - l) < ε

/-- `u` est une suite de Cauchy. -/
def Cauchy (u : Suite) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ m n, N ≤ m → N ≤ n → vabs (u m - u n) < ε

/-- Propriété d'Archimède : `1 / (N + 1)` devient plus petit que n'importe quel `ε > 0`. -/
theorem archimede (ε : Rat) (h : 0 < ε) : ∃ N : Nat, 1 / ((N : Rat) + 1) < ε := by
  refine ⟨(1 / ε).ceil.toNat, ?_⟩
  have h1 : (1 / ε) ≤ ((1 / ε).ceil : Rat) := Rat.le_ceil
  have h2 : ((1 / ε).ceil : Int) ≤ (((1 / ε).ceil.toNat : Nat) : Int) := Int.self_le_toNat _
  have h3 : ((1 / ε).ceil : Rat) ≤ ((((1 / ε).ceil.toNat : Nat) : Int) : Rat) :=
    Rat.intCast_le_intCast.mpr h2
  rw [Rat.intCast_natCast] at h3
  have hM : 1 / ε ≤ (((1 / ε).ceil.toNat : Nat) : Rat) := Rat.le_trans h1 h3
  have h6 : ε * (1 / ε) ≤ ε * (((1 / ε).ceil.toNat : Nat) : Rat) :=
    Rat.mul_le_mul_of_nonneg_left hM (Rat.le_of_lt h)
  have h5 : ε * (1 / ε) = 1 := by grind
  rw [Rat.div_lt_iff (by grind)]
  grind

end Parcours.Analyse
