import Exercices.Naturels.Pont
import Exercices.Logique.Bilan

/-!
# Les listes (cours)

Une liste d'éléments de type `α` est :
- soit la liste vide `nil`,
- soit `x ∷ l` : un élément `x` (la tête) suivi d'une liste `l` (la queue). `∷` se tape `\::`.

Comme pour ℕ, on reconstruit tout à la main (Lean a déjà `List`, on le retrouvera au Pont).
Les longueurs sont des `Nat` de Lean : le Pont des entiers est franchi, donc `omega` est permis.

## Définitions (par récurrence sur la liste)
- concaténation `l₁ ++ l₂` : `nil ++ l = l`, `(x ∷ l₁) ++ l₂ = x ∷ (l₁ ++ l₂)`
- `longueur`, `miroir` (renversement), `map f`, `somme`, `filtre p`, `prendre n`, `jeter n`
- appartenance `x ∈ l`

La tactique `induction l with | nil => … | cons x l ih => …` fait une récurrence sur une liste.
`simp only [concat_cons, …]` ou `rw` déplient les définitions ; beaucoup de cas sont `rfl`.

## Ressources
- [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/) — programmer en Lean.
- [Liste (Wikipédia)](https://fr.wikipedia.org/wiki/Liste_%28informatique%29)

---
*Exercice* `Listes.Definitions` · difficulté ★☆☆☆☆
-/

namespace Parcours.Listes

inductive Liste (α : Type) where
  | nil : Liste α
  | cons (x : α) (l : Liste α) : Liste α
  deriving DecidableEq, Repr

infixr:67 " ∷ " => Liste.cons

namespace Liste

variable {α β : Type}

/-- Concaténation. -/
def concat : Liste α → Liste α → Liste α
  | nil, l => l
  | x ∷ l₁, l₂ => x ∷ concat l₁ l₂

instance : Append (Liste α) := ⟨concat⟩

theorem nil_concat (l : Liste α) : nil ++ l = l := rfl
theorem cons_concat (x : α) (l₁ l₂ : Liste α) : (x ∷ l₁) ++ l₂ = x ∷ (l₁ ++ l₂) := rfl

def longueur : Liste α → Nat
  | nil => 0
  | _ ∷ l => longueur l + 1

theorem longueur_nil : longueur (nil : Liste α) = 0 := rfl
theorem longueur_cons (x : α) (l : Liste α) : longueur (x ∷ l) = longueur l + 1 := rfl

/-- Le miroir (renversement) : `miroir [1, 2, 3] = [3, 2, 1]`. -/
def miroir : Liste α → Liste α
  | nil => nil
  | x ∷ l => miroir l ++ (x ∷ nil)

theorem miroir_nil : miroir (nil : Liste α) = nil := rfl
theorem miroir_cons (x : α) (l : Liste α) : miroir (x ∷ l) = miroir l ++ (x ∷ nil) := rfl

def map (f : α → β) : Liste α → Liste β
  | nil => nil
  | x ∷ l => f x ∷ map f l

theorem map_nil (f : α → β) : map f nil = nil := rfl
theorem map_cons (f : α → β) (x : α) (l : Liste α) : map f (x ∷ l) = f x ∷ map f l := rfl

def somme : Liste Nat → Nat
  | nil => 0
  | x ∷ l => x + somme l

def filtre (p : α → Bool) : Liste α → Liste α
  | nil => nil
  | x ∷ l => if p x then x ∷ filtre p l else filtre p l

def prendre : Nat → Liste α → Liste α
  | 0, _ => nil
  | _ + 1, nil => nil
  | n + 1, x ∷ l => x ∷ prendre n l

def jeter : Nat → Liste α → Liste α
  | 0, l => l
  | _ + 1, nil => nil
  | n + 1, _ ∷ l => jeter n l

def foldr (f : α → β → β) (b : β) : Liste α → β
  | nil => b
  | x ∷ l => f x (foldr f b l)

def foldl (f : β → α → β) (b : β) : Liste α → β
  | nil => b
  | x ∷ l => foldl f (f b x) l

/-- L'appartenance : `x ∈ l`. -/
inductive Mem (x : α) : Liste α → Prop where
  | tete (l : Liste α) : Mem x (x ∷ l)
  | queue (y : α) {l : Liste α} : Mem x l → Mem x (y ∷ l)

instance : Membership α (Liste α) := ⟨fun l x => Mem x l⟩

theorem mem_cons (x y : α) (l : Liste α) : x ∈ y ∷ l ↔ x = y ∨ x ∈ l := by
  constructor
  · intro h
    cases h with
    | tete => exact Or.inl rfl
    | queue _ h => exact Or.inr h
  · rintro (rfl | h)
    · exact Mem.tete l
    · exact Mem.queue y h

theorem not_mem_nil (x : α) : ¬x ∈ (nil : Liste α) := by
  intro h
  cases h

end Liste
end Parcours.Listes
