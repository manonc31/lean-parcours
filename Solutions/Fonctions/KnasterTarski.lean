/- @parcours
titre: Le théorème de Knaster–Tarski
difficulte: 4
requiert: Fonctions.Ensembles
indice: Candidat : l'intersection de tous les `t` tels que `F t ⊆ t`. En Lean : `let s : Ens α := fun x => ∀ t : Ens α, F t ⊆ t → x ∈ t`.
indice: Étape 1 : `F s ⊆ s`. Soit `x ∈ F s` et `t` avec `F t ⊆ t`. Comme `s ⊆ t` (par définition de `s`), `F s ⊆ F t ⊆ t`.
indice: Étape 2 : `s ⊆ F s`. Il suffit de voir que `F s` est l'un des `t` : `F (F s) ⊆ F s` par monotonie et l'étape 1.
indice: Conclure avec `subset_antisymm`.
-/
import Solutions.Fonctions.Ensembles

/-!
# Le théorème du point fixe de Knaster–Tarski

Soit `F : Ens α → Ens α` **croissante** : si `s ⊆ t` alors `F s ⊆ F t`.
Alors `F` a un **point fixe** : un ensemble `s` tel que `F s = s`.

Ce théorème (1928/1955) est partout en informatique : sémantique des boucles, définitions
inductives, analyse de programmes… et il donne une preuve élégante de Cantor–Schröder–Bernstein.

## À prouver
`knaster_tarski (F : Ens α → Ens α) (hF : ∀ s t, s ⊆ t → F s ⊆ F t) : ∃ s, F s = s`

## Ressources
- [Théorème de Knaster-Tarski (Wikipédia)](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_de_Knaster-Tarski)
-/

namespace Parcours.Fonctions

theorem knaster_tarski {α : Type} (F : Ens α → Ens α) (hF : ∀ s t, s ⊆ t → F s ⊆ F t) :
    ∃ s, F s = s := by -- @exo
  let s : Ens α := fun x => ∀ t : Ens α, F t ⊆ t → x ∈ t
  have h1 : F s ⊆ s := by
    intro x hx t ht
    have hst : s ⊆ t := fun y hy => hy t ht
    exact ht x (hF s t hst x hx)
  have h2 : s ⊆ F s := by
    intro x hx
    exact hx (F s) (hF (F s) s h1)
  exact ⟨s, subset_antisymm h1 h2⟩

end Parcours.Fonctions

#verifier
