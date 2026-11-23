import Exercices.Fonctions.Definitions

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

---
*Exercice* `Fonctions.Ensembles` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Fonctions.Ensembles` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Fonctions

variable {α : Type} {s t u : Ens α}

theorem inter_comm : s ∩ t = t ∩ s := by
  sorry

theorem inter_union_distrib : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) := by
  sorry

theorem compl_union : (s ∪ t)ᶜ = sᶜ ∩ tᶜ := by
  sorry

theorem subset_trans (h1 : s ⊆ t) (h2 : t ⊆ u) : s ⊆ u := by
  sorry

theorem subset_antisymm (h1 : s ⊆ t) (h2 : t ⊆ s) : s = t := by
  sorry

end Parcours.Fonctions

#verifier
