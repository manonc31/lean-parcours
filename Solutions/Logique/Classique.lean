/- @parcours
titre: La logique classique
difficulte: 3
indice: `rcases Classical.em P with hp | hnp` : deux cas, `P` vrai ou `P` faux.
indice: Pour `double_neg_elim`, dans le cas `hnp : ¬P`, tu as aussi `h : ¬¬P` : contradiction (`exact absurd hnp h`).
indice: Pour `non_et`, sens `→` : raisonne par cas sur `P`. Si `P` est vrai, alors `¬Q` (sinon on aurait `P ∧ Q`).
indice: `contraposee_inverse` : utilise `double_neg_elim`.
-/
import Solutions.Logique.DeMorgan

/-!
# La logique classique

Jusqu'ici tout était **constructif**. La logique classique ajoute le **tiers exclu** :
pour toute proposition `P`, `P ∨ ¬P`. En Lean : `Classical.em P : P ∨ ¬P`.

C'est un **axiome** (en réalité, Lean le déduit de l'axiome du choix — voir l'exercice
« Diaconescu »). Il est autorisé dès maintenant.

Tactique pratique : `by_cases h : P` crée deux cas, l'un avec `h : P`, l'autre avec `h : ¬P`.
Aussi : `Classical.byContradiction` (raisonnement par l'absurde) :
`apply Classical.byContradiction` puis `intro h` te donne `h : ¬(but)` et le but `False`.

## À prouver
1. `double_neg_elim : ¬¬P → P`
2. `non_et : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q`
3. `contraposee_inverse : (¬Q → ¬P) → (P → Q)`
4. `impl_ou : (P → Q) ↔ ¬P ∨ Q`

## Ressources
- [Principe du tiers exclu (Wikipédia)](https://fr.wikipedia.org/wiki/Principe_du_tiers_exclu)
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/), section *Classical Logic*.
-/

namespace Parcours.Logique

variable {P Q : Prop}

theorem double_neg_elim (h : ¬¬P) : P := by -- @exo
  rcases Classical.em P with hp | hnp
  · exact hp
  · exact absurd hnp h

theorem non_et : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by -- @exo
  constructor
  · intro h
    rcases Classical.em P with hp | hnp
    · right
      intro hq
      exact h ⟨hp, hq⟩
    · left
      exact hnp
  · exact non_et_de_ou

theorem contraposee_inverse (h : ¬Q → ¬P) : P → Q := by -- @exo
  intro hp
  apply double_neg_elim
  intro hnq
  exact h hnq hp

theorem impl_ou : (P → Q) ↔ ¬P ∨ Q := by -- @exo
  constructor
  · intro h
    rcases Classical.em P with hp | hnp
    · exact Or.inr (h hp)
    · exact Or.inl hnp
  · rintro (hnp | hq) hp
    · exact absurd hp hnp
    · exact hq

end Parcours.Logique

#verifier
