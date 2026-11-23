/- @parcours
titre: Calcul ensembliste
difficulte: 2
indice: Pour une égalité d'ensembles : `apply ext`, `intro x`, puis tu dois prouver un `↔`.
indice: `x ∈ s ∩ t` est par définition `x ∈ s ∧ x ∈ t` : tu peux directement faire `rintro ⟨hs, ht⟩`, ou d'abord `simp only [mem_inter, mem_union, mem_compl]` pour voir les connecteurs.
indice: Après `simp only [...]`, ce sont exactement les exercices de la branche Logique (distributivité, De Morgan…). Le jeton `logique` est débloqué ici : `simp` ou `and_comm`, `not_or` sont permis !
-/
import Solutions.Fonctions.Definitions

/-!
# Calcul ensembliste

Les opérations sur les ensembles sont les connecteurs logiques déguisés :
`∩` c'est `∧`, `∪` c'est `∨`, le complémentaire c'est `¬`, `⊆` c'est `→`.

## À prouver
1. `inter_comm : s ∩ t = t ∩ s`
2. `inter_union_distrib : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u)`
3. `compl_union : (s ∪ t)ᶜ = sᶜ ∩ tᶜ`
4. `subset_trans : s ⊆ t → t ⊆ u → s ⊆ u`
5. `subset_antisymm : s ⊆ t → t ⊆ s → s = t`
-/

namespace Parcours.Fonctions

variable {α : Type} {s t u : Ens α}

theorem inter_comm : s ∩ t = t ∩ s := by -- @exo
  apply ext
  intro x
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

theorem inter_union_distrib : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) := by -- @exo
  apply ext
  intro x
  simp only [mem_inter, mem_union]
  constructor
  · rintro ⟨hs, ht | hu⟩
    · exact Or.inl ⟨hs, ht⟩
    · exact Or.inr ⟨hs, hu⟩
  · rintro (⟨hs, ht⟩ | ⟨hs, hu⟩)
    · exact ⟨hs, Or.inl ht⟩
    · exact ⟨hs, Or.inr hu⟩

theorem compl_union : (s ∪ t)ᶜ = sᶜ ∩ tᶜ := by -- @exo
  apply ext
  intro x
  simp only [mem_compl, mem_union, mem_inter]
  exact not_or

theorem subset_trans (h1 : s ⊆ t) (h2 : t ⊆ u) : s ⊆ u := by -- @exo
  intro x hx
  exact h2 x (h1 x hx)

theorem subset_antisymm (h1 : s ⊆ t) (h2 : t ⊆ s) : s = t := by -- @exo
  apply ext
  intro x
  exact ⟨h1 x, h2 x⟩

end Parcours.Fonctions

#verifier
