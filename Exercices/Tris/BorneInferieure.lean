import Exercices.Tris.Definitions
import Exercices.Recurrence.Definitions

/-!
# 💀 On ne peut pas trier plus vite que n log n

Un algorithme de tri « par comparaisons » est un **arbre de décision** : à chaque nœud, il
compare deux positions `i` et `j` de l'entrée et va à gauche si `v i < v j`, à droite sinon.
Une feuille donne le résultat : la liste des positions dans l'ordre trié.

Théorème : tout arbre qui trie correctement **toutes** les entrées sans doublon de taille `n`
a une profondeur `d` telle que `n! ≤ 2^d`, c'est-à-dire `d ≥ log₂(n!) ≈ n log₂ n`.
Le tri fusion est donc **optimal**.

Boss sans solution de référence.

## À prouver
`borne_inferieure (t : Arbre n) (h : t.Trie) : fact n ≤ 2 ^ t.profondeur`

## Ressources
- [Tri par comparaison, borne inférieure (Wikipédia)](https://fr.wikipedia.org/wiki/Tri_par_comparaison)

---
*Exercice* `Tris.BorneInferieure` · difficulté ★★★★★

💡 Indices : `./parcours indice Tris.BorneInferieure` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Tris

open Parcours.Recurrence

/-- Un arbre de décision qui compare des positions d'une entrée de taille `n`. -/
inductive Arbre (n : Nat) where
  | feuille (σ : List (Fin n)) : Arbre n
  | noeud (i j : Fin n) (siInf sinon : Arbre n) : Arbre n

def Arbre.executer {n : Nat} (v : Fin n → Nat) : Arbre n → List (Fin n)
  | .feuille σ => σ
  | .noeud i j a b => if v i < v j then a.executer v else b.executer v

def Arbre.profondeur {n : Nat} : Arbre n → Nat
  | .feuille _ => 0
  | .noeud _ _ a b => max a.profondeur b.profondeur + 1

/-- L'arbre trie : pour toute entrée sans doublon, la sortie est une permutation des positions
qui range les valeurs dans l'ordre strictement croissant. -/
def Arbre.Trie {n : Nat} (t : Arbre n) : Prop :=
  ∀ v : Fin n → Nat, (∀ i j, v i = v j → i = j) →
    (t.executer v).Perm (List.finRange n) ∧ ((t.executer v).map v).Pairwise (· < ·)

theorem borne_inferieure {n : Nat} (t : Arbre n) (h : t.Trie) : fact n ≤ 2 ^ t.profondeur := by
  sorry

end Parcours.Tris

#verifier
