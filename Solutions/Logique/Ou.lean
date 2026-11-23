/- @parcours
titre: Le « ou »
difficulte: 1
requiert: Logique.Et
indice: Pour prouver `P ∨ Q`, choisis un côté : `left` (il reste à prouver `P`) ou `right` (il reste `Q`).
indice: Pour utiliser `h : P ∨ Q`, fais une disjonction de cas : `rcases h with hp | hq`. Tu obtiens deux buts, un avec `hp : P`, l'autre avec `hq : Q`.
indice: Pour `ou_assoc`, `rcases h with (hp | hq) | hr` découpe tout d'un coup en trois cas.
-/
import ParcoursOutils

/-!
# Le « ou » (∨)

Une preuve de `P ∨ Q` est **soit** une preuve de `P` (`Or.inl hp`), **soit** une preuve de `Q` (`Or.inr hq`).

- **Construire** : `left` puis prouver `P`, ou `right` puis prouver `Q`.
- **Utiliser** `h : P ∨ Q` : raisonner par cas avec `rcases h with hp | hq`
  (ou `cases h with | inl hp => … | inr hq => …`).

Le symbole `∨` se tape `\or`.

## À prouver
1. `ou_gauche` : de `P`, déduire `P ∨ Q`.
2. `ou_comm` : de `P ∨ Q`, déduire `Q ∨ P`.
3. `ou_elim` : si `P → R` et `Q → R`, alors `P ∨ Q → R`.
4. `ou_assoc` : de `(P ∨ Q) ∨ R`, déduire `P ∨ (Q ∨ R)`.
-/

namespace Parcours.Logique

variable {P Q R : Prop}

theorem ou_gauche (hp : P) : P ∨ Q := by -- @exo
  left
  exact hp

theorem ou_comm (h : P ∨ Q) : Q ∨ P := by -- @exo
  rcases h with hp | hq
  · right
    exact hp
  · left
    exact hq

theorem ou_elim (hpr : P → R) (hqr : Q → R) (h : P ∨ Q) : R := by -- @exo
  rcases h with hp | hq
  · exact hpr hp
  · exact hqr hq

theorem ou_assoc (h : (P ∨ Q) ∨ R) : P ∨ (Q ∨ R) := by -- @exo
  rcases h with (hp | hq) | hr
  · exact Or.inl hp
  · exact Or.inr (Or.inl hq)
  · exact Or.inr (Or.inr hr)

end Parcours.Logique

#verifier
