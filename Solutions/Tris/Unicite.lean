/- @parcours
titre: Il n'y a qu'une façon d'être trié
difficulte: 4
indice: Récurrence sur `l₁` en généralisant `l₂`, puis `cases l₂`.
indice: Cas `a :: l₁` et `b :: l₂` : montre `a = b`. On a `a ∈ b :: l₂` et `b ∈ a :: l₁` (par la permutation). Si `a ≠ b`, alors `b ≤ a` (car `l₂` triée après `b`) et `a ≤ b` : contradiction.
indice: Puis `List.Perm.cons_inv : (a :: l₁) ~ (a :: l₂) → l₁ ~ l₂` et l'hypothèse de récurrence.
indice: Cas `[]` et `b :: l₂` : une permutation de `[]` est vide (`List.Perm.nil_eq`, ou compare les longueurs avec `List.Perm.length_eq`).
-/
import Solutions.Tris.Definitions

/-!
# Il n'y a qu'une façon d'être trié

Deux listes triées qui sont permutation l'une de l'autre sont **égales**.
Conséquence : tous les algorithmes de tri corrects donnent **exactement** le même résultat.

## À prouver
`trie_unique : Trie l₁ → Trie l₂ → l₁.Perm l₂ → l₁ = l₂`
-/

namespace Parcours.Tris

theorem trie_unique (l₁ l₂ : List Nat) (h₁ : Trie l₁) (h₂ : Trie l₂) (hp : l₁.Perm l₂) :
    l₁ = l₂ := by -- @exo
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons b l₂ => have := hp.length_eq; simp at this
  | cons a l₁ ih =>
    cases l₂ with
    | nil => have := hp.length_eq; simp at this
    | cons b l₂ =>
      rw [trie_cons] at h₁ h₂
      have hab : a = b := by
        have ha : a ∈ b :: l₂ := hp.mem_iff.mp List.mem_cons_self
        have hb : b ∈ a :: l₁ := hp.mem_iff.mpr List.mem_cons_self
        rcases List.mem_cons.mp ha with h | h
        · exact h
        · rcases List.mem_cons.mp hb with h' | h'
          · exact h'.symm
          · have := h₂.1 a h
            have := h₁.1 b h'
            omega
      subst hab
      rw [ih l₂ h₁.2 h₂.2 hp.cons_inv]

end Parcours.Tris

#verifier
