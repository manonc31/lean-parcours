import Exercices.Informatique.Expressions

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

---
*Exercice* `Informatique.Regex` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Informatique.Regex` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
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

theorem reconnait_vide_de_nullable (r : Regex α) (h : nullable r = true) : Reconnait r [] := by
  sorry

theorem nullable_de_reconnait {r : Regex α} {w : List α} (h : Reconnait r w) (hw : w = []) :
    nullable r = true := by
  sorry

theorem nullable_correct (r : Regex α) : nullable r = true ↔ Reconnait r [] := by
  sorry

end Parcours.Info

#verifier
