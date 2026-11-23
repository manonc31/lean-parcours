/- @parcours
titre: Répéter et compter
difficulte: 2
indice: Toutes les preuves : récurrence (sur `n` pour `repeter`, sur `l₁` pour `compter_concat`).
indice: `compter x (y ∷ l)` vaut `(if y = x then 1 else 0) + compter x l` : après `simp only [compter]`, utilise `split` puis `omega`.
-/
import Solutions.Listes.Longueur

/-!
# Répéter et compter

- `repeter n x` : la liste `[x, x, …, x]` (`n` fois).
- `compter x l` : le nombre d'occurrences de `x` dans `l`.

## À prouver
1. `longueur_repeter : longueur (repeter n x) = n`
2. `compter_repeter : compter x (repeter n x) = n`
3. `compter_concat : compter x (l₁ ++ l₂) = compter x l₁ + compter x l₂`
-/

namespace Parcours.Listes.Liste

def repeter {α : Type} : Nat → α → Liste α
  | 0, _ => nil
  | n + 1, x => x ∷ repeter n x

def compter (x : Nat) : Liste Nat → Nat
  | nil => 0
  | y ∷ l => (if y = x then 1 else 0) + compter x l

theorem longueur_repeter {α : Type} (n : Nat) (x : α) : longueur (repeter n x) = n := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    show longueur (repeter n x) + 1 = n + 1
    rw [ih]

theorem compter_repeter (n x : Nat) : compter x (repeter n x) = n := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    show (if x = x then 1 else 0) + compter x (repeter n x) = n + 1
    rw [ih]
    simp
    omega

theorem compter_concat (x : Nat) (l₁ l₂ : Liste Nat) :
    compter x (l₁ ++ l₂) = compter x l₁ + compter x l₂ := by -- @exo
  induction l₁ with
  | nil => exact (Nat.zero_add _).symm
  | cons y l ih =>
    rw [cons_concat]
    simp only [compter, ih]
    omega

end Parcours.Listes.Liste

#verifier
