/- @parcours
celebre: 25
titre: Cantor–Schröder–Bernstein
difficulte: 5
genre: boss
requiert: Fonctions.Images, Fonctions.Bijections
indice: Applique Knaster–Tarski à `F S := (g '' (f '' S)ᶜ)ᶜ`. (Vérifie qu'elle est croissante : deux complémentaires inversent deux fois l'inclusion.) Soit `A` un point fixe.
indice: Conséquence clé du point fixe : `x ∉ A ↔ x ∈ g '' (f '' A)ᶜ`. Donc si `x ∉ A`, il existe `y ∉ f '' A` avec `g y = x`.
indice: Définis `h x := if hx : x ∈ A then f x else Classical.choose (… preuve que x a un antécédent par g hors de f '' A …)`. Il faut `haveI := Classical.propDecidable`.
indice: Injectivité : 3 cas. Les deux dans `A` : injectivité de `f`. Les deux hors de `A` : on applique `g`. Un dans `A`, l'autre non : l'un est dans `f '' A`, l'autre non, contradiction.
indice: Surjectivité de `h`, pour `y` : si `y ∈ f '' A`, facile. Sinon, `x := g y` n'est pas dans `A`, et `h x` est un `y'` avec `g y' = g y`, donc `y' = y`.
-/
import Solutions.Fonctions.KnasterTarski
import Solutions.Fonctions.Images
import Solutions.Fonctions.Bijections

/-!
# 💀 Le théorème de Cantor–Schröder–Bernstein

> S'il existe une injection de `α` dans `β` et une injection de `β` dans `α`,
> alors il existe une **bijection** entre `α` et `β`.

Autrement dit : si `|α| ≤ |β|` et `|β| ≤ |α|` alors `|α| = |β|`, même pour des ensembles infinis.
Énoncé par Cantor (1887), prouvé par Bernstein et Schröder (1897), avec une longue histoire de preuves fausses.

Indication générale : la preuve via **Knaster–Tarski** (que tu as prouvé) est la plus courte.
Elle demande de bien manipuler images, complémentaires, et l'axiome du choix.

## À prouver
`cantor_schroeder_bernstein (f : α → β) (g : β → α) (hf : Injective f) (hg : Injective g) :
  ∃ h : α → β, Bijective h`

## Ressources
- [Théorème de Cantor-Bernstein (Wikipédia)](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_de_Cantor-Bernstein)
-/

namespace Parcours.Fonctions

theorem cantor_schroeder_bernstein {α β : Type} (f : α → β) (g : β → α)
    (hf : Injective f) (hg : Injective g) : ∃ h : α → β, Bijective h := by -- @exo
  haveI := Classical.propDecidable
  let F : Ens α → Ens α := fun S => (g '' (f '' S)ᶜ)ᶜ
  have hF : ∀ s t, s ⊆ t → F s ⊆ F t := by
    intro s t hst x hx hxt
    apply hx
    obtain ⟨y, hy, hyx⟩ := hxt
    refine ⟨y, ?_, hyx⟩
    intro hys
    apply hy
    obtain ⟨a, ha, hay⟩ := hys
    exact ⟨a, hst a ha, hay⟩
  obtain ⟨A, hA⟩ := knaster_tarski F hF
  -- clé : hors de A, on est dans g '' (f '' A)ᶜ
  have cle : ∀ x, x ∉ A → ∃ y, y ∉ f '' A ∧ g y = x := by
    intro x hx
    apply Classical.byContradiction
    intro hne
    apply hx
    rw [← hA]
    intro hxg
    obtain ⟨y, hy, hyx⟩ := hxg
    exact hne ⟨y, hy, hyx⟩
  have dans : ∀ y, y ∉ f '' A → g y ∉ A := by
    intro y hy hgy
    rw [← hA] at hgy
    exact hgy ⟨y, hy, rfl⟩
  let h : α → β := fun x => if hx : x ∈ A then f x else Classical.choose (cle x hx)
  have h_in : ∀ x (hx : x ∈ A), h x = f x := fun x hx => dite_eq_left hx
  have h_out : ∀ x (hx : x ∉ A), h x = Classical.choose (cle x hx) := fun x hx => dite_eq_right hx
  have spec : ∀ x (hx : x ∉ A), h x ∉ f '' A ∧ g (h x) = x := by
    intro x hx
    rw [h_out x hx]
    exact Classical.choose_spec (cle x hx)
  refine ⟨h, ?_, ?_⟩
  · intro a b hab
    by_cases ha : a ∈ A <;> by_cases hb : b ∈ A
    · rw [h_in a ha, h_in b hb] at hab
      exact hf a b hab
    · exfalso
      apply (spec b hb).1
      rw [← hab, h_in a ha]
      exact ⟨a, ha, rfl⟩
    · exfalso
      apply (spec a ha).1
      rw [hab, h_in b hb]
      exact ⟨b, hb, rfl⟩
    · rw [← (spec a ha).2, ← (spec b hb).2, hab]
  · intro y
    by_cases hy : y ∈ f '' A
    · obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨x, h_in x hx⟩
    · have hgy := dans y hy
      refine ⟨g y, ?_⟩
      exact hg _ _ (spec (g y) hgy).2

end Parcours.Fonctions

#verifier
