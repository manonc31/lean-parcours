/- @parcours
titre: Listes triées et permutations
difficulte: 1
genre: cours
requiert: Listes.Pont
-/
import Solutions.Listes.Pont
import Solutions.Naturels.Transfert
import Solutions.Logique.Bilan

/-!
# Listes triées et permutations (cours)

On travaille avec les listes de Lean, `List Nat` (le Pont des listes est franchi : tous les
lemmes `List.*` sont permis).

Un algorithme de tri est **correct** si, pour toute liste `l`, le résultat :
1. est **trié** : `Trie (tri l)` ;
2. est une **permutation** de `l` : `(tri l).Perm l` (mêmes éléments, mêmes multiplicités).

`Trie l` est défini comme `l.Pairwise (· ≤ ·)` : chaque élément est ≤ à tous ceux qui le suivent.

## Lemmes utiles (bibliothèque)
- `List.Perm.refl`, `.symm`, `.trans`, `.cons x`, `.append`, `List.perm_middle`, `List.Perm.swap`
- `List.Perm.mem_iff : l₁ ~ l₂ → (a ∈ l₁ ↔ a ∈ l₂)`
- `trie_cons`, `trie_append` (ci-dessous), `List.mem_cons`, `List.mem_append`, `List.mem_filter`

## Récurrence fonctionnelle
Pour prouver une propriété d'une fonction récursive `f`, `fun_induction f l with …` suit exactement
les appels récursifs (même quand ce n'est pas une récurrence « structurelle »).

## Ressources
- [Algorithme de tri (Wikipédia)](https://fr.wikipedia.org/wiki/Algorithme_de_tri)
-/

namespace Parcours.Tris

/-- Une liste est triée si chaque élément est ≤ à tous les suivants. -/
def Trie (l : List Nat) : Prop := l.Pairwise (· ≤ ·)

theorem trie_nil : Trie [] := List.Pairwise.nil

theorem trie_cons {x : Nat} {l : List Nat} : Trie (x :: l) ↔ (∀ y ∈ l, x ≤ y) ∧ Trie l :=
  List.pairwise_cons

theorem trie_append {l₁ l₂ : List Nat} :
    Trie (l₁ ++ l₂) ↔ Trie l₁ ∧ Trie l₂ ∧ ∀ a ∈ l₁, ∀ b ∈ l₂, a ≤ b :=
  List.pairwise_append

end Parcours.Tris
