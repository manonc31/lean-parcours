/- @parcours
titre: Fonctions et ensembles
difficulte: 1
genre: cours
-/
import Solutions.Logique.Bilan

/-!
# Fonctions et ensembles (cours)

## Fonctions
Pour `f : α → β` :
- `Injective f` : deux antécédents différents ont des images différentes : `∀ a b, f a = f b → a = b` ;
- `Surjective f` : tout `y` a un antécédent : `∀ y, ∃ x, f x = y` ;
- `Bijective f` : les deux.

La composée `g ∘ f` (tapé `\comp`) est la fonction `fun x => g (f x)`.

## Ensembles
Un **ensemble** d'éléments de `α` est ici une propriété : `Ens α := α → Prop`.
`x ∈ s` (tapé `\in`) signifie simplement `s x`. On définit `⊆` (`\sub`), `∪` (`\cup`),
`∩` (`\cap`), le complémentaire `sᶜ` (`\^c`), l'image `f '' s` et l'image réciproque `f ⁻¹' s`.

Pour prouver que deux ensembles sont égaux : `apply ext` puis montrer `∀ x, x ∈ s ↔ x ∈ t`.
Pour déplier une définition : `show …` ou `simp only [mem_inter, mem_union, …]`.

## Ressources
- [Application injective (Wikipédia)](https://fr.wikipedia.org/wiki/Injection_%28math%C3%A9matiques%29)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/), chapitre *Sets and Functions*.
-/

namespace Parcours.Fonctions

variable {α β γ : Type}

def Injective (f : α → β) : Prop := ∀ a b, f a = f b → a = b
def Surjective (f : α → β) : Prop := ∀ y, ∃ x, f x = y
def Bijective (f : α → β) : Prop := Injective f ∧ Surjective f

/-- Un ensemble d'éléments de `α`, vu comme une propriété. -/
def Ens (α : Type) := α → Prop

instance : Membership α (Ens α) := ⟨fun s a => s a⟩
instance : HasSubset (Ens α) := ⟨fun s t => ∀ x, x ∈ s → x ∈ t⟩
instance : Union (Ens α) := ⟨fun s t => fun x => x ∈ s ∨ x ∈ t⟩
instance : Inter (Ens α) := ⟨fun s t => fun x => x ∈ s ∧ x ∈ t⟩

/-- Le complémentaire. -/
def compl (s : Ens α) : Ens α := fun x => x ∉ s
postfix:max "ᶜ" => compl

/-- L'image de `s` par `f`. -/
def image (f : α → β) (s : Ens α) : Ens β := fun y => ∃ x, x ∈ s ∧ f x = y
infix:80 " '' " => image

/-- L'image réciproque de `t` par `f`. -/
def preimage (f : α → β) (t : Ens β) : Ens α := fun x => f x ∈ t
infix:80 " ⁻¹' " => preimage

theorem mem_def (s : Ens α) (x : α) : x ∈ s ↔ s x := Iff.rfl
theorem mem_inter (s t : Ens α) (x : α) : x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t := Iff.rfl
theorem mem_union (s t : Ens α) (x : α) : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t := Iff.rfl
theorem mem_compl (s : Ens α) (x : α) : x ∈ sᶜ ↔ x ∉ s := Iff.rfl
theorem mem_image (f : α → β) (s : Ens α) (y : β) : y ∈ f '' s ↔ ∃ x, x ∈ s ∧ f x = y := Iff.rfl
theorem mem_preimage (f : α → β) (t : Ens β) (x : α) : x ∈ f ⁻¹' t ↔ f x ∈ t := Iff.rfl
theorem subset_def (s t : Ens α) : s ⊆ t ↔ ∀ x, x ∈ s → x ∈ t := Iff.rfl

/-- Extensionnalité : deux ensembles ayant les mêmes éléments sont égaux. -/
theorem ext {s t : Ens α} (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t :=
  funext fun x => propext (h x)

end Parcours.Fonctions
