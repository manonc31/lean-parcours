/- @parcours
titre: Les expressions régulières
difficulte: 3
indice: Sens `→` (`reconnait_vide_de_nullable`) : récurrence sur `r`. Pour `concat r s`, si `nullable r && nullable s = true`, les deux sont vrais (`Bool.and_eq_true`), et `[] = [] ++ []`.
indice: Sens `←` (`nullable_de_reconnait`) : récurrence sur la dérivation `h`, avec l'hypothèse `hw : w = []`. Cas `concat` : `List.append_eq_nil_iff` donne `u = []` et `v = []`.
indice: Cas impossible (`car a` avec `[a] = []`) : `cases hw`.
-/
import Solutions.Informatique.Expressions

/-!
# Les expressions régulières

Une expression régulière décrit un ensemble de mots : `a*b` (des `a` puis un `b`), `(ab|c)*`…
On en donne la **sémantique** par une relation inductive `Reconnait r w` (« `r` reconnaît le mot `w` »).

`nullable r` **calcule** si `r` reconnaît le mot vide. Prouve que ce calcul est correct.
C'est la première brique de l'algorithme de **Brzozowski** (boss suivant) qui fait marcher
`grep` et compagnie.

## À prouver
`nullable_correct (r : Regex α) : nullable r = true ↔ Reconnait r []`

## Ressources
- [Expression régulière (Wikipédia)](https://fr.wikipedia.org/wiki/Expression_r%C3%A9guli%C3%A8re)
-/

namespace Parcours.Info

inductive Regex (α : Type) where
  | vide
  | eps
  | car (a : α)
  | union (r s : Regex α)
  | concat (r s : Regex α)
  | etoile (r : Regex α)

open Regex

variable {α : Type}

inductive Reconnait : Regex α → List α → Prop
  | eps : Reconnait eps []
  | car (a : α) : Reconnait (car a) [a]
  | union_g {r s : Regex α} {w : List α} : Reconnait r w → Reconnait (union r s) w
  | union_d {r s : Regex α} {w : List α} : Reconnait s w → Reconnait (union r s) w
  | concat {r s : Regex α} {u v : List α} : Reconnait r u → Reconnait s v → Reconnait (concat r s) (u ++ v)
  | etoile_nil {r : Regex α} : Reconnait (etoile r) []
  | etoile_cons {r : Regex α} {u v : List α} :
      Reconnait r u → Reconnait (etoile r) v → Reconnait (etoile r) (u ++ v)

def nullable : Regex α → Bool
  | vide => false
  | eps => true
  | car _ => false
  | union r s => nullable r || nullable s
  | concat r s => nullable r && nullable s
  | etoile _ => true

theorem reconnait_vide_de_nullable (r : Regex α) (h : nullable r = true) : Reconnait r [] := by -- @exo
  induction r with
  | vide => cases h
  | eps => exact Reconnait.eps
  | car a => cases h
  | union r s ihr ihs =>
    simp only [nullable, Bool.or_eq_true] at h
    rcases h with h | h
    · exact Reconnait.union_g (ihr h)
    · exact Reconnait.union_d (ihs h)
  | concat r s ihr ihs =>
    simp only [nullable, Bool.and_eq_true] at h
    exact Reconnait.concat (u := []) (v := []) (ihr h.1) (ihs h.2)
  | etoile r _ => exact Reconnait.etoile_nil

theorem nullable_de_reconnait {r : Regex α} {w : List α} (h : Reconnait r w) (hw : w = []) :
    nullable r = true := by -- @exo
  induction h with
  | eps => rfl
  | car a => cases hw
  | union_g _ ih => simp [nullable, ih hw]
  | union_d _ ih => simp [nullable, ih hw]
  | concat _ _ ih₁ ih₂ =>
    obtain ⟨hu, hv⟩ := List.append_eq_nil_iff.mp hw
    simp [nullable, ih₁ hu, ih₂ hv]
  | etoile_nil => rfl
  | etoile_cons _ _ _ _ => rfl

theorem nullable_correct (r : Regex α) : nullable r = true ↔ Reconnait r [] := by -- @exo
  exact ⟨reconnait_vide_de_nullable r, fun h => nullable_de_reconnait h rfl⟩

end Parcours.Info

#verifier
