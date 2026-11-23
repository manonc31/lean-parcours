import Exercices.Programmes.Definitions

/-!
# Chercher dans une liste

`chercher p l` renvoie le premier élément de `l` qui vérifie `p` (ou `none` s'il n'y en a pas).

## À prouver
1. `chercher_some` : si on trouve `x`, alors `x ∈ l` et `p x`.
2. `chercher_none` : si on ne trouve rien, aucun élément ne vérifie `p`.

---
*Exercice* `Programmes.Recherche` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Programmes.Recherche` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

def chercher (p : Nat → Bool) : List Nat → Option Nat
  | [] => none
  | x :: l => if p x then some x else chercher p l

theorem chercher_some (p : Nat → Bool) (l : List Nat) (x : Nat) (h : chercher p l = some x) :
    x ∈ l ∧ p x = true := by
  sorry

theorem chercher_none (p : Nat → Bool) (l : List Nat) (h : chercher p l = none) :
    ∀ x ∈ l, p x = false := by
  sorry

end Parcours.Prog

#verifier
