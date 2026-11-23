/- @parcours
titre: L'équivalence
difficulte: 2
indice: Pour prouver `P ↔ Q`, `constructor` donne deux buts : `P → Q` et `Q → P`.
indice: Avec `h : P ↔ Q`, `h.mp : P → Q` et `h.mpr : Q → P`. On peut aussi écrire `exact ⟨f, g⟩` avec `f : P → Q` et `g : Q → P`.
indice: Pour `et_comm_iff`, réutilise ton `et_comm` des deux côtés !
-/
import Solutions.Logique.Et
import Solutions.Logique.Ou

/-!
# L'équivalence (↔)

`P ↔ Q` signifie `(P → Q) ∧ (Q → P)`. Le symbole se tape `\iff`.

- **Construire** : `constructor`, puis prouver les deux sens.
- **Utiliser** `h : P ↔ Q` : `h.mp` (sens direct), `h.mpr` (sens réciproque),
  ou `rw [h]` pour remplacer `P` par `Q` dans le but !

Remarque : ce fichier **importe** tes exercices « Et » et « Ou » : tu peux y réutiliser
les théorèmes que tu as prouvés (`et_comm`, `ou_comm`…). C'est le principe de tout le parcours.

## À prouver
1. `equiv_refl : P ↔ P`
2. `equiv_symm : (P ↔ Q) → (Q ↔ P)`
3. `equiv_trans : (P ↔ Q) → (Q ↔ R) → (P ↔ R)`
4. `et_comm_iff : P ∧ Q ↔ Q ∧ P`
5. `ou_comm_iff : P ∨ Q ↔ Q ∨ P`
-/

namespace Parcours.Logique

variable {P Q R : Prop}

theorem equiv_refl : P ↔ P := by -- @exo
  constructor
  · intro h
    exact h
  · intro h
    exact h

theorem equiv_symm (h : P ↔ Q) : Q ↔ P := by -- @exo
  exact ⟨h.mpr, h.mp⟩

theorem equiv_trans (h1 : P ↔ Q) (h2 : Q ↔ R) : P ↔ R := by -- @exo
  exact ⟨fun hp => h2.mp (h1.mp hp), fun hr => h1.mpr (h2.mpr hr)⟩

theorem et_comm_iff : P ∧ Q ↔ Q ∧ P := by -- @exo
  exact ⟨et_comm, et_comm⟩

theorem ou_comm_iff : P ∨ Q ↔ Q ∨ P := by -- @exo
  exact ⟨ou_comm, ou_comm⟩

end Parcours.Logique

#verifier
