import Exercices.Arithmetique.Decomposition
import Exercices.Arithmetique.LemmeEuclide

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

---
*Exercice* `Arithmetique.Unicite` · difficulté ★★★★☆

💡 Indices : `./parcours indice Arithmetique.Unicite` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Arith

theorem premier_divise_prod {p : Nat} (hp : Premier p) (l : List Nat) (h : p ∣ l.prod) :
    ∃ q ∈ l, p ∣ q := by
  sorry

theorem prod_perm {l l' : List Nat} (h : l.Perm l') : l.prod = l'.prod := by
  sorry

theorem unicite_decomposition (l₁ l₂ : List Nat) (h₁ : ∀ p ∈ l₁, Premier p)
    (h₂ : ∀ p ∈ l₂, Premier p) (h : l₁.prod = l₂.prod) : l₁.Perm l₂ := by
  sorry

end Parcours.Arith

#verifier
