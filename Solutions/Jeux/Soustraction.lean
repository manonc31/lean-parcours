/- @parcours
titre: Le jeu de soustraction 1-3-4
difficulte: 3
requiert: Jeux.FortBoyard
indice: Récurrence forte (`induction n using Nat.strongRecOn`), avec les hypothèses pour `n − 1`, `n − 3` et `n − 4`.
indice: Transforme les booléens en propositions (`Bool.or_eq_true`, `Bool.and_eq_true`…), puis distingue les valeurs de `gagne134 (n − 1)`, etc. (`cases g : …`), et `omega`.
-/
import Solutions.Recurrence.Definitions

/-!
# Le jeu de soustraction 1-3-4

Un tas de `n` jetons ; chacun son tour, on en retire 1, 3 ou 4. Celui qui ne peut plus jouer a
perdu. Qui gagne ? En calculant les premières positions, on voit apparaître un motif de période 7 :
les positions **perdantes** (pour celui qui doit jouer) sont celles où `n ≡ 0` ou `2 (mod 7)`.

Une position est gagnante s'il existe un coup qui mène à une position perdante.

## À prouver
`gagne134_spec : gagne134 n = true ↔ n % 7 ≠ 0 ∧ n % 7 ≠ 2`

## Ressources
- [Jeu de soustraction (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Subtraction_game)
-/

namespace Parcours.Jeux

def gagne134 (n : Nat) : Bool :=
  if h : n = 0 then false
  else !gagne134 (n - 1) || (3 ≤ n && !gagne134 (n - 3)) || (4 ≤ n && !gagne134 (n - 4))
termination_by n
decreasing_by all_goals omega

theorem gagne134_spec (n : Nat) : gagne134 n = true ↔ (n % 7 ≠ 0 ∧ n % 7 ≠ 2) := by -- @exo
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [gagne134]
    by_cases h0 : n = 0
    · simp [h0]
    · have i1 := ih (n - 1) (by omega)
      have i3 := ih (n - 3) (by omega)
      have i4 := ih (n - 4) (by omega)
      simp only [h0, ↓reduceDIte, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_true_eq]
      cases g1 : gagne134 (n - 1) <;> cases g3 : gagne134 (n - 3) <;>
        cases g4 : gagne134 (n - 4) <;> simp_all <;> omega

end Parcours.Jeux

#verifier
