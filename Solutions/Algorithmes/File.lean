/- @parcours
titre: Une file avec deux piles
difficulte: 3
indice: `contenu_enfiler` : déplie (`simp only [File.enfiler, File.contenu]`), puis `List.reverse_cons` et `List.append_assoc`.
indice: `defiler_correct` : déplie `File.defiler` et fais des cas : `rcases f with ⟨_ | ⟨y, r⟩, arr⟩`, puis sur `arr.reverse` (`cases h : arr.reverse`).
indice: Dans le second cas, `List.reverse_eq_nil_iff` et le fait que `contenu = avant ++ arriere.reverse`.
-/
import Solutions.Algorithmes.Definitions

/-!
# Une file avec deux piles

Une **file** (premier arrivé, premier servi) se programme avec deux listes : `avant` (d'où l'on
retire) et `arriere` (où l'on ajoute, à l'envers). Quand `avant` est vide, on retourne `arriere`.
Chaque opération coûte en moyenne un temps constant (« coût amorti »). C'est la file standard
des langages fonctionnels.

Le **contenu** abstrait de la file est `avant ++ arriere.reverse`.

## À prouver
1. `contenu_enfiler : (f.enfiler x).contenu = f.contenu ++ [x]`
2. `defiler_correct : f.defiler = some (x, f') → f.contenu = x :: f'.contenu`
3. `defiler_vide : f.defiler = none → f.contenu = []`
-/

namespace Parcours.Algo

structure File where
  avant : List Nat
  arriere : List Nat

def File.contenu (f : File) : List Nat := f.avant ++ f.arriere.reverse

def File.enfiler (x : Nat) (f : File) : File := ⟨f.avant, x :: f.arriere⟩

def File.defiler (f : File) : Option (Nat × File) :=
  match f.avant with
  | x :: r => some (x, ⟨r, f.arriere⟩)
  | [] =>
    match f.arriere.reverse with
    | [] => none
    | x :: r => some (x, ⟨r, []⟩)

theorem contenu_enfiler (x : Nat) (f : File) : (f.enfiler x).contenu = f.contenu ++ [x] := by -- @exo
  simp only [File.enfiler, File.contenu, List.reverse_cons, List.append_assoc]

theorem defiler_correct (f f' : File) (x : Nat) (h : f.defiler = some (x, f')) :
    f.contenu = x :: f'.contenu := by -- @exo
  rcases f with ⟨_ | ⟨y, r⟩, arr⟩
  · simp only [File.defiler] at h
    cases hr : arr.reverse with
    | nil => simp [hr] at h
    | cons z s =>
      simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [File.contenu, hr]
  · simp only [File.defiler, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [File.contenu]

theorem defiler_vide (f : File) (h : f.defiler = none) : f.contenu = [] := by -- @exo
  rcases f with ⟨_ | ⟨y, r⟩, arr⟩
  · simp only [File.defiler] at h
    cases hr : arr.reverse with
    | nil => simp [File.contenu, hr]
    | cons z s => simp [hr] at h
  · simp [File.defiler] at h

end Parcours.Algo

#verifier
