/- @parcours
titre: Les anagrammes
difficulte: 3
requiert: Combinatoire.Menus
indice: `longueur_inserer` et `mem_inserer` : récurrence sur `l`.
indice: `longueur_perms` : la longueur d'un `flatMap` est la somme des longueurs (`List.length_flatMap`) ; chaque terme vaut `|l| + 1`. `List.map_congr_left` permet de remplacer la fonction par une constante.
indice: `anna`, `kayak` : des calculs.
-/
import Solutions.Combinatoire.Definitions

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
-/

namespace Parcours.Combi

open Parcours.Recurrence

def inserer (x : Nat) : List Nat → List (List Nat)
  | [] => [[x]]
  | y :: l => (x :: y :: l) :: (inserer x l).map (y :: ·)

def perms : List Nat → List (List Nat)
  | [] => [[]]
  | x :: l => (perms l).flatMap (inserer x)

theorem longueur_inserer (x : Nat) (l : List Nat) : (inserer x l).length = l.length + 1 := by -- @exo
  induction l with
  | nil => rfl
  | cons y l ih => simp [inserer, ih]

theorem mem_inserer (x : Nat) (l p : List Nat) (h : p ∈ inserer x l) : p.length = l.length + 1 := by -- @exo
  induction l generalizing p with
  | nil =>
    simp [inserer] at h
    simp [h]
  | cons y l ih =>
    simp only [inserer, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨q, hq, rfl⟩
    · simp
    · simp [ih q hq]

theorem mem_perms (l p : List Nat) (h : p ∈ perms l) : p.length = l.length := by -- @exo
  induction l generalizing p with
  | nil =>
    simp [perms] at h
    simp [h]
  | cons x l ih =>
    simp only [perms, List.mem_flatMap] at h
    obtain ⟨q, hq, hp⟩ := h
    rw [mem_inserer x q p hp, ih q hq]
    rfl

theorem longueur_perms (l : List Nat) : (perms l).length = fact l.length := by -- @exo
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [perms, List.length_flatMap, List.length_cons, fact_succ]
    rw [List.map_congr_left (g := fun _ => l.length + 1)
      (fun q hq => by rw [longueur_inserer, mem_perms l q hq])]
    rw [List.map_const', List.sum_replicate_nat, ih, Nat.mul_comm]

theorem anna : (perms [0, 1, 1, 0]).eraseDups.length = 6 := by -- @exo
  decide

theorem kayak : (perms [0, 1, 2, 1, 0]).eraseDups.length = 30 := by -- @exo
  decide +kernel

end Parcours.Combi

#verifier
