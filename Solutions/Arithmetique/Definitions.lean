/- @parcours
titre: Divisibilité, PGCD, nombres premiers
difficulte: 1
genre: cours
requiert: Recurrence.Gauss
-/
import Solutions.Recurrence.Definitions
import Solutions.Listes.Pont

/-!
# Divisibilité, PGCD, nombres premiers (cours)

## Divisibilité
`a ∣ b` (tapé `\|`, ce n'est PAS la barre `|` du clavier !) signifie `∃ c, b = a * c`.
- Pour le prouver : `exact ⟨c, preuve⟩`.
- Pour l'utiliser : `obtain ⟨c, hc⟩ := h` (ou `obtain ⟨c, rfl⟩ := h` pour remplacer directement `b`).

⚠️ Les lemmes de la bibliothèque sur `∣`, `Nat.gcd`, les nombres premiers… ne sont **pas**
débloqués (ce serait trop facile) : tu vas les reconstruire. Le Pont arithmétique les débloquera.
Par contre `%`, `/`, `omega`, `grind` et tous les autres lemmes de `Nat` sont permis.

## PGCD
`pgcd a b` est défini par l'**algorithme d'Euclide** : `pgcd a 0 = a`, et si `b ≠ 0`,
`pgcd a b = pgcd b (a % b)`. Pour raisonner dessus : la **récurrence fonctionnelle**
`fun_induction pgcd a b with | case1 a => … | case2 a b hb ih => …` (elle suit exactement
les appels récursifs de l'algorithme).

## Nombres premiers
`Premier p` : `2 ≤ p` et les seuls diviseurs de `p` sont `1` et `p`.

## Congruences
`a ≡ b [mod n]` signifie `a % n = b % n`.

## Ressources
- [Algorithme d'Euclide (Wikipédia)](https://fr.wikipedia.org/wiki/Algorithme_d%27Euclide)
- [Nombre premier (Wikipédia)](https://fr.wikipedia.org/wiki/Nombre_premier)
-/

namespace Parcours.Arith

open Parcours.Recurrence

theorem divise_def (a b : Nat) : a ∣ b ↔ ∃ c, b = a * c := Iff.rfl

set_option linter.unusedVariables false in
/-- Le PGCD, par l'algorithme d'Euclide. -/
def pgcd (a b : Nat) : Nat :=
  if h : b = 0 then a else pgcd b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

theorem pgcd_zero (a : Nat) : pgcd a 0 = a := by
  rw [pgcd]
  simp

theorem pgcd_rec (a b : Nat) (hb : b ≠ 0) : pgcd a b = pgcd b (a % b) := by
  rw [pgcd]
  simp [hb]

def Premier (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

def Congru (n a b : Nat) : Prop := a % n = b % n

notation:50 a " ≡ " b " [mod " n "]" => Congru n a b

theorem fact_pos (n : Nat) : 0 < fact n := by
  induction n with
  | zero => decide
  | succ n ih => rw [fact_succ]; exact Nat.mul_pos (by omega) ih

end Parcours.Arith
