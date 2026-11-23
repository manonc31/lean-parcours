/- @parcours
titre: Le lemme des poignées de main
difficulte: 4
indice: Étape 1 : `(L.filter (· < n + 1)).length = (L.filter (· < n)).length + L.count n` (récurrence sur `L` ; `List.filter_cons`, `List.count_cons`, puis `split` et `omega`).
indice: Étape 2 : `((List.range n).map (fun v => L.count v)).sum = (L.filter (· < n)).length` (récurrence sur `n` ; `List.range_succ`, `List.map_append`, `List.sum_append`, et l'étape 1).
indice: Étape 3 : si tous les sommets sont `< n`, le `filter` ne retire rien (`List.filter_eq_self`), et `(extremites g).length = 2 * g.length` (récurrence sur `g`).
-/
import Solutions.Graphes.Definitions

/-!
# Le lemme des poignées de main

Dans une soirée, si on additionne pour chaque invité le nombre de mains qu'il a serrées, on
obtient un nombre **pair** : chaque poignée de main est comptée deux fois.
En graphes : la somme des degrés vaut deux fois le nombre d'arêtes (Euler, 1736).

## À prouver
1. `longueur_extremites : (extremites g).length = 2 * g.length`
2. `poignees_de_mains : (∀ e ∈ g, e.1 < n ∧ e.2 < n) → ((List.range n).map (degre g)).sum = 2 * g.length`

## Ressources
- [Lemme des poignées de main (Wikipédia)](https://fr.wikipedia.org/wiki/Lemme_des_poign%C3%A9es_de_main)
-/

namespace Parcours.Graphes

theorem longueur_extremites (g : Graphe) : (extremites g).length = 2 * g.length := by -- @exo
  induction g with
  | nil => rfl
  | cons e g ih =>
    rw [extremites_cons]
    simp only [List.length_cons, ih]
    omega

theorem poignees_de_mains (g : Graphe) (n : Nat) (h : ∀ e ∈ g, e.1 < n ∧ e.2 < n) :
    ((List.range n).map (degre g)).sum = 2 * g.length := by -- @exo
  have filtre_succ : ∀ (L : List Nat) (k : Nat),
      (L.filter (fun x => decide (x < k + 1))).length =
        (L.filter (fun x => decide (x < k))).length + L.count k := by
    intro L k
    induction L with
    | nil => rfl
    | cons x L ih =>
      simp only [List.filter_cons, List.count_cons, beq_iff_eq, decide_eq_true_eq]
      split <;> split <;> split <;> (try simp only [List.length_cons]) <;> omega
  have somme : ∀ (L : List Nat) (k : Nat),
      ((List.range k).map (fun v => L.count v)).sum = (L.filter (fun x => decide (x < k))).length := by
    intro L k
    induction k with
    | zero =>
      simp only [List.range_zero, List.map_nil, List.sum_nil]
      induction L with
      | nil => rfl
      | cons y L ihL => simpa [List.filter_cons] using ihL
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, filtre_succ]
      simp
  have htout : (extremites g).filter (fun x => decide (x < n)) = extremites g := by
    rw [List.filter_eq_self]
    intro a ha
    simp only [extremites, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at ha
    obtain ⟨e, he, rfl | rfl⟩ := ha
    · simpa using (h e he).1
    · simpa using (h e he).2
  show ((List.range n).map (fun v => (extremites g).count v)).sum = 2 * g.length
  rw [somme, htout, longueur_extremites]

end Parcours.Graphes

#verifier
