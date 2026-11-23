import ParcoursOutils

/-!
# Les entiers naturels de Peano (cours)

Ce fichier ne contient pas d'exercice : il **définit** notre propre type `ℕ`, à partir de rien.
Lean possède déjà `Nat`, mais nous allons tout reconstruire : comme ça, la bibliothèque
ne peut pas faire le travail à ta place !

Un entier naturel est :
- soit `zero` (noté `0`),
- soit `succ n`, le **successeur** de `n` (c'est-à-dire `n + 1`).

Ainsi `3` est `succ (succ (succ 0))`. C'est la définition de Peano (1889).

L'addition est définie **par récurrence sur le second argument** :
- `a + 0 = a`                     (théorème `add_zero`)
- `a + succ b = succ (a + b)`     (théorème `add_succ`)

Ces deux égalités sont vraies **par définition** (preuve : `rfl`). Tout le reste
(`0 + a = a`, la commutativité, l'associativité…) devra être prouvé, par toi, dans les exercices.

## La récurrence
Grâce à l'attribut `induction_eliminator` ci-dessous, la tactique `induction n with`
produit deux cas : `zero` (prouver pour `0`) et `succ n ih` (prouver pour `succ n`,
sachant `ih` : la propriété pour `n`).

## Astuce : `#eval`
Tu peux calculer : `#eval (2 + 3 : ℕ)` affiche `5`.

## Ressources
- [Axiomes de Peano (Wikipédia)](https://fr.wikipedia.org/wiki/Axiomes_de_Peano)
- [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4) — exactement ce chemin, en version jeu.

---
*Exercice* `Naturels.Base` · difficulté ★☆☆☆☆
-/

namespace Parcours

/-- Les entiers naturels, construits à partir de rien. -/
inductive ℕ where
  | zero : ℕ
  | succ (n : ℕ) : ℕ
  deriving DecidableEq

namespace ℕ

/-- Conversion depuis les entiers de Lean, pour pouvoir écrire `0`, `1`, `2`… -/
def ofNat : Nat → ℕ
  | 0 => zero
  | n + 1 => succ (ofNat n)

instance instOfNat (n : Nat) : OfNat ℕ n := ⟨ofNat n⟩

/-- Conversion vers les entiers de Lean (utile pour l'affichage, et pour le Pont). -/
def toNat : ℕ → Nat
  | zero => 0
  | succ n => toNat n + 1

instance : Repr ℕ := ⟨fun n _ => repr n.toNat⟩

theorem zero_eq_zero : zero = 0 := rfl

/-- Principe de récurrence (affiché avec `0` plutôt que `zero`). -/
@[induction_eliminator]
def recurrence {P : ℕ → Sort _} (zero : P 0) (succ : (n : ℕ) → P n → P (succ n)) : (n : ℕ) → P n
  | .zero => zero
  | .succ n => succ n (recurrence zero succ n)

/-- Raisonnement par cas : `n = 0` ou `n = succ m`. -/
@[cases_eliminator]
def parCas {P : ℕ → Sort _} (zero : P 0) (succ : (n : ℕ) → P (succ n)) : (n : ℕ) → P n
  | .zero => zero
  | .succ n => succ n

/-- L'addition, par récurrence sur le second argument. -/
def add : ℕ → ℕ → ℕ
  | a, zero => a
  | a, succ b => succ (add a b)

instance : Add ℕ := ⟨add⟩

theorem add_zero (a : ℕ) : a + 0 = a := rfl
theorem add_succ (a b : ℕ) : a + succ b = succ (a + b) := rfl

theorem one_eq_succ_zero : (1 : ℕ) = succ 0 := rfl
theorem two_eq_succ_one : (2 : ℕ) = succ 1 := rfl
theorem three_eq_succ_two : (3 : ℕ) = succ 2 := rfl
theorem four_eq_succ_three : (4 : ℕ) = succ 3 := rfl

/-- Axiome de Peano : `succ` est injective. (Lean le prouve automatiquement.) -/
theorem succ_inj {a b : ℕ} (h : succ a = succ b) : a = b := by
  injection h

/-- Axiome de Peano : `0` n'est le successeur de personne. -/
theorem zero_ne_succ (a : ℕ) : (0 : ℕ) ≠ succ a := by
  intro h
  cases h

end ℕ
end Parcours
