import Exercices.Algorithmes.Definitions

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

---
*Exercice* `Algorithmes.File` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Algorithmes.File` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
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

theorem contenu_enfiler (x : Nat) (f : File) : (f.enfiler x).contenu = f.contenu ++ [x] := by
  sorry

theorem defiler_correct (f f' : File) (x : Nat) (h : f.defiler = some (x, f')) :
    f.contenu = x :: f'.contenu := by
  sorry

theorem defiler_vide (f : File) (h : f.defiler = none) : f.contenu = [] := by
  sorry

end Parcours.Algo

#verifier
