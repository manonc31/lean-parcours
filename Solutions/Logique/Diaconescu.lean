/- @parcours
titre: Diaconescu : le choix implique le tiers exclu
difficulte: 4
interdit: Classical.em, Classical.byContradiction, Classical.propDecidable, Classical.byCases, Classical.not_not, Classical.dec*, Classical.typeDecidable*, Classical.exists_or_forall_not, Classical.or_iff_not_imp*, Classical.not_forall*, Classical.not_imp*, Classical.epsilon*, Classical.axiomOfChoice, Classical.skolem, Decidable.em, Decidable.byContradiction
requiert: Logique.Classique, Logique.Egalite
indice: Définis deux propriétés : `U x := (x = True) ∨ P` et `V x := (x = False) ∨ P`. Elles sont satisfaites (par `True` et `False`).
indice: Choisis `u := Classical.choose exU` et `v := Classical.choose exV`, avec `Classical.choose_spec` : `u = True ∨ P` et `v = False ∨ P`.
indice: Premier fait : `u ≠ v ∨ P` (par cas sur les deux spécifications ; `True ≠ False`).
indice: Second fait : `P → u = v`. Car si `P`, alors `U = V` (par `funext` et `propext`) ; et choisir dans deux prédicats égaux donne le même élément. Astuce : prouve `∀ (e1 : ∃ x, U x) (e2 : ∃ x, V x), Classical.choose e1 = Classical.choose e2` en faisant `rw [hUV]` puis `intro e1 e2; rfl`.
indice: Conclusion : soit `P`, soit `u ≠ v`, et dans ce cas `¬P` (sinon `u = v`).
-/
import ParcoursOutils

/-!
# Le théorème de Diaconescu

L'**axiome du choix** dit que dans toute famille d'ensembles non vides, on peut choisir un élément
de chacun. En Lean : `Classical.choose (h : ∃ x, p x)` est un `x` vérifiant `p`
(`Classical.choose_spec h : p (Classical.choose h)`).

Le théorème de Diaconescu (1975) : **l'axiome du choix implique le tiers exclu** (avec l'extensionnalité
des fonctions `funext` et des propositions `propext`). C'est exactement comme ça que Lean définit
`Classical.em` !

Ici tu as droit à `Classical.choose`, `Classical.choose_spec`, `funext`, `propext`,
mais **pas** au tiers exclu ni à `by_cases` (le vérificateur le refuserait).

## À prouver
`diaconescu (P : Prop) : P ∨ ¬P`

## Ressources
- [Théorème de Diaconescu (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Diaconescu%27s_theorem)
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/), chapitre *Axioms and Computation*.
-/

namespace Parcours.Logique

theorem diaconescu (P : Prop) : P ∨ ¬P := by -- @exo
  let U : Prop → Prop := fun x => x = True ∨ P
  let V : Prop → Prop := fun x => x = False ∨ P
  have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
  have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
  have hu : Classical.choose exU = True ∨ P := Classical.choose_spec exU
  have hv : Classical.choose exV = False ∨ P := Classical.choose_spec exV
  have ne_ou_p : Classical.choose exU ≠ Classical.choose exV ∨ P := by
    rcases hu with hu | hp
    · rcases hv with hv | hp
      · left
        rw [hu, hv]
        intro h
        exact h ▸ trivial
      · right
        exact hp
    · right
      exact hp
  have p_egal : P → Classical.choose exU = Classical.choose exV := by
    intro hp
    have hUV : U = V := funext fun x => propext ⟨fun _ => Or.inr hp, fun _ => Or.inr hp⟩
    have h : ∀ (e1 : ∃ x, U x) (e2 : ∃ x, V x), Classical.choose e1 = Classical.choose e2 := by
      rw [hUV]
      intro e1 e2
      rfl
    exact h exU exV
  rcases ne_ou_p with hne | hp
  · right
    intro hp
    exact hne (p_egal hp)
  · left
    exact hp

end Parcours.Logique

#verifier
