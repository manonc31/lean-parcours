/- @parcours
titre: Faux et négation
difficulte: 2
requiert: Logique.Implication
indice: `¬P` est par définition `P → False` : pour prouver `¬P`, commence par `intro hp`.
indice: De `hp : P` et `hnp : ¬P`, `hnp hp : False`. Et de `False`, on déduit n'importe quoi : `exact (hnp hp).elim`, ou `exfalso` puis `exact hnp hp`.
indice: Pour `triple_neg`, dans le sens `→`, utilise `double_neg_intro`.
-/
import ParcoursOutils

/-!
# Faux et négation

- `False` est la proposition **sans preuve**. Si tu arrives à prouver `False`, tes hypothèses
  sont contradictoires, et tu peux alors prouver n'importe quoi (`False.elim`, ou la tactique `exfalso`).
- `¬P` (tapé `\not`) est **défini** comme `P → False`.

Tactiques utiles : `exfalso` (remplace le but par `False`), `contradiction`
(trouve tout seul deux hypothèses contradictoires), `absurd`.

## À prouver
1. `faux_elim : False → P`
2. `non_contradiction : ¬(P ∧ ¬P)`
3. `contraposee : (P → Q) → (¬Q → ¬P)`
4. `double_neg_intro : P → ¬¬P`
5. `triple_neg : ¬¬¬P ↔ ¬P`

Remarque : la réciproque `¬¬P → P` n'est **pas** prouvable ainsi ! Il faudra la logique classique.

## Ressources
- [Logique intuitionniste (Wikipédia)](https://fr.wikipedia.org/wiki/Logique_intuitionniste)
-/

namespace Parcours.Logique

variable {P Q : Prop}

theorem faux_elim (h : False) : P := by -- @exo
  exact h.elim

theorem non_contradiction : ¬(P ∧ ¬P) := by -- @exo
  rintro ⟨hp, hnp⟩
  exact hnp hp

theorem contraposee (h : P → Q) : ¬Q → ¬P := by -- @exo
  intro hnq hp
  exact hnq (h hp)

theorem double_neg_intro (hp : P) : ¬¬P := by -- @exo
  intro hnp
  exact hnp hp

theorem triple_neg : ¬¬¬P ↔ ¬P := by -- @exo
  constructor
  · intro h hp
    exact h (double_neg_intro hp)
  · intro hnp hnnp
    exact hnnp hnp

end Parcours.Logique

#verifier
