import Exercices.Combinatoire.Definitions

/-!
# Les anagrammes

Combien de façons de ranger `n` objets distincts ? `n! = n × (n − 1) × ⋯ × 1`. Le programme
`perms` construit toutes les permutations : pour ranger `x :: l`, on range `l` puis on **insère**
`x` à chacune des `|l| + 1` places possibles.

Avec des lettres répétées, il y a moins d'anagrammes : « ANNA » n'en a que `4! / (2! × 2!) = 6`.

## À prouver
1. `longueur_inserer`, `mem_inserer`, `mem_perms` : les longueurs.
2. `longueur_perms : (perms l).length = fact l.length`
3. `anna : (perms [0, 1, 1, 0]).eraseDups.length = 6` et `kayak` : 30 anagrammes.

---
*Exercice* `Combinatoire.Anagrammes` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Combinatoire.Anagrammes` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Combi

open Parcours.Recurrence

def inserer (x : Nat) : List Nat → List (List Nat)
  | [] => [[x]]
  | y :: l => (x :: y :: l) :: (inserer x l).map (y :: ·)

def perms : List Nat → List (List Nat)
  | [] => [[]]
  | x :: l => (perms l).flatMap (inserer x)

theorem longueur_inserer (x : Nat) (l : List Nat) : (inserer x l).length = l.length + 1 := by
  sorry

theorem mem_inserer (x : Nat) (l p : List Nat) (h : p ∈ inserer x l) : p.length = l.length + 1 := by
  sorry

theorem mem_perms (l p : List Nat) (h : p ∈ perms l) : p.length = l.length := by
  sorry

theorem longueur_perms (l : List Nat) : (perms l).length = fact l.length := by
  sorry

theorem anna : (perms [0, 1, 1, 0]).eraseDups.length = 6 := by
  sorry

theorem kayak : (perms [0, 1, 2, 1, 0]).eraseDups.length = 30 := by
  sorry

end Parcours.Combi

#verifier
