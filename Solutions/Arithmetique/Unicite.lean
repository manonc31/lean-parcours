/- @parcours
celebre: 80
titre: Décomposition en facteurs premiers (unicité)
difficulte: 4
indice: Lemme 1 : si `p` premier divise `l.prod`, il divise un élément de `l` (récurrence sur `l` + lemme d'Euclide).
indice: Lemme 2 : si `p` et `q` sont premiers et `p ∣ q`, alors `p = q`.
indice: Théorème : récurrence sur `l₁` en généralisant `l₂`. Cas `p :: l₁` : `p` divise `l₂.prod`, donc `p ∈ l₂` (lemmes 1 et 2). Alors `l₂ ~ p :: l₂.erase p` (`List.perm_cons_erase`), et en simplifiant par `p`, `l₁.prod = (l₂.erase p).prod`.
indice: `prod_perm`, `List.Perm.cons`, `List.Perm.trans`, `List.Perm.symm`, `List.mem_of_mem_erase` sont tes amis.
-/
import Solutions.Arithmetique.Decomposition
import Solutions.Arithmetique.LemmeEuclide

/-!
# Décomposition en facteurs premiers (unicité)

Le **théorème fondamental de l'arithmétique** : la décomposition est unique, à l'ordre près.
« À l'ordre près » se dit : les deux listes sont des **permutations** l'une de l'autre
(`l₁.Perm l₂`, ou `l₁ ~ l₂`).

## À prouver
1. `premier_divise_prod : Premier p → p ∣ l.prod → ∃ q ∈ l, p ∣ q`
2. `prod_perm : l.Perm l' → l.prod = l'.prod` (par récurrence sur la preuve de permutation : `induction h with | nil | cons | swap | trans`)
3. `unicite_decomposition : (∀ p ∈ l₁, Premier p) → (∀ p ∈ l₂, Premier p) → l₁.prod = l₂.prod → l₁.Perm l₂`

## Ressources
- [Théorème fondamental de l'arithmétique (Wikipédia)](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_fondamental_de_l%27arithm%C3%A9tique)
-/

namespace Parcours.Arith

theorem premier_divise_prod {p : Nat} (hp : Premier p) (l : List Nat) (h : p ∣ l.prod) :
    ∃ q ∈ l, p ∣ q := by -- @exo
  induction l with
  | nil =>
    rw [List.prod_nil] at h
    have := divise_un h
    have := hp.1
    omega
  | cons a l ih =>
    rw [List.prod_cons] at h
    rcases premier_divise_mul hp h with h1 | h1
    · exact ⟨a, List.mem_cons_self, h1⟩
    · obtain ⟨q, hq, hpq⟩ := ih h1
      exact ⟨q, List.mem_cons_of_mem a hq, hpq⟩

theorem prod_perm {l l' : List Nat} (h : l.Perm l') : l.prod = l'.prod := by -- @exo
  induction h with
  | nil => rfl
  | cons x _ ih => rw [List.prod_cons, List.prod_cons, ih]
  | swap x y l => rw [List.prod_cons, List.prod_cons, List.prod_cons, List.prod_cons, Nat.mul_left_comm]
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

theorem unicite_decomposition (l₁ l₂ : List Nat) (h₁ : ∀ p ∈ l₁, Premier p)
    (h₂ : ∀ p ∈ l₂, Premier p) (h : l₁.prod = l₂.prod) : l₁.Perm l₂ := by -- @exo
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => exact List.Perm.refl _
    | cons q l₂ =>
      exfalso
      rw [List.prod_nil, List.prod_cons] at h
      have hq := (h₂ q List.mem_cons_self).1
      have := divise_un ⟨l₂.prod, h⟩
      omega
  | cons p l₁ ih =>
    have hp := h₁ p List.mem_cons_self
    have hdiv : p ∣ l₂.prod := by
      rw [← h, List.prod_cons]
      exact divise_mul_droite (divise_refl p) _
    obtain ⟨q, hq, hpq⟩ := premier_divise_prod hp l₂ hdiv
    have hpq' : p = q := ((h₂ q hq).2 p hpq).resolve_left (by have := hp.1; omega)
    subst hpq'
    have hperm := List.perm_cons_erase hq
    have hprod : l₁.prod = (l₂.erase p).prod := by
      have h' : p * l₁.prod = p * (l₂.erase p).prod := by
        rw [← List.prod_cons, ← List.prod_cons, h, prod_perm hperm]
      exact Nat.eq_of_mul_eq_mul_left (by have := hp.1; omega) h'
    have ih' := ih (l₂.erase p) (fun r hr => h₁ r (List.mem_cons_of_mem p hr))
      (fun r hr => h₂ r (List.mem_of_mem_erase hr)) hprod
    exact (ih'.cons p).trans hperm.symm

end Parcours.Arith

#verifier
