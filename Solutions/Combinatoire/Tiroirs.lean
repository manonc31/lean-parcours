/- @parcours
titre: Le principe des tiroirs
difficulte: 4
indice: `tiroirs` : récurrence sur `n` en généralisant `l`. Cas `0` : tous les éléments sont `< 0`, donc `l = []`.
indice: Cas `n + 1` : par cas sur `n ∈ l`. Si oui, retire-le (`l.erase n`) : la liste obtenue est sans doublon (`List.Nodup.erase`), ses éléments sont `< n` (car `≠ n` : `List.Nodup.mem_erase_iff`), et sa longueur est `l.length - 1` (`List.length_erase_of_mem`).
indice: `treize_personnes` : par l'absurde, `mois` serait injective. Applique `tiroirs` à `(List.finRange 13).map (fun i => (mois i).val)`.
indice: Pour montrer que cette liste est sans doublon : `List.Nodup` est `List.Pairwise (· ≠ ·)`, et `List.Pairwise.map` transporte la propriété depuis `List.nodup_finRange 13`.
-/
import Solutions.Combinatoire.Definitions

/-!
# Le principe des tiroirs

> Si on range `n + 1` chaussettes dans `n` tiroirs, un tiroir contient au moins deux chaussettes.

Version « liste » : une liste **sans doublon** dont tous les éléments sont `< n` a au plus `n` éléments.
Conséquence amusante : parmi 13 personnes, deux sont nées le même mois.

## À prouver
1. `tiroirs : l.Nodup → (∀ x ∈ l, x < n) → l.length ≤ n`
2. `treize_personnes (mois : Fin 13 → Fin 12) : ∃ i j, i ≠ j ∧ mois i = mois j`

## Ressources
- [Principe des tiroirs (Wikipédia)](https://fr.wikipedia.org/wiki/Principe_des_tiroirs)
-/

namespace Parcours.Combi

theorem tiroirs {n : Nat} {l : List Nat} (hnd : l.Nodup) (h : ∀ x ∈ l, x < n) : l.length ≤ n := by -- @exo
  induction n generalizing l with
  | zero =>
    cases l with
    | nil => exact Nat.le_refl 0
    | cons x l => exact absurd (h x List.mem_cons_self) (Nat.not_lt_zero x)
  | succ n ih =>
    by_cases hn : n ∈ l
    · have h1 := List.length_erase_of_mem hn
      have h2 : (l.erase n).length ≤ n := by
        apply ih (hnd.erase n)
        intro x hx
        obtain ⟨hne, hxl⟩ := (List.Nodup.mem_erase_iff hnd).mp hx
        have := h x hxl
        omega
      have := List.length_pos_of_mem hn
      omega
    · apply Nat.le_succ_of_le
      apply ih hnd
      intro x hx
      have := h x hx
      have : x ≠ n := fun e => hn (e ▸ hx)
      omega

theorem treize_personnes (mois : Fin 13 → Fin 12) : ∃ i j, i ≠ j ∧ mois i = mois j := by -- @exo
  apply Classical.byContradiction
  intro h
  have hinj : ∀ i j, mois i = mois j → i = j := fun i j hij =>
    Classical.byContradiction fun hne => h ⟨i, j, hne, hij⟩
  have hnd : ((List.finRange 13).map (fun i => (mois i).val)).Nodup :=
    List.Pairwise.map _ (fun a b hab hf => hab (hinj a b (Fin.ext hf))) (List.nodup_finRange 13)
  have hlt : ∀ x ∈ (List.finRange 13).map (fun i => (mois i).val), x < 12 := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact (mois i).isLt
  have := tiroirs hnd hlt
  simp at this

end Parcours.Combi

#verifier
