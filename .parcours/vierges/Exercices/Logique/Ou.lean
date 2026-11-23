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

---
*Exercice* `Logique.Ou` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Logique.Ou` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Logique

variable {P Q R : Prop}

theorem ou_gauche (hp : P) : P ∨ Q := by
  sorry

theorem ou_comm (h : P ∨ Q) : Q ∨ P := by
  sorry

theorem ou_elim (hpr : P → R) (hqr : Q → R) (h : P ∨ Q) : R := by
  sorry

theorem ou_assoc (h : (P ∨ Q) ∨ R) : P ∨ (Q ∨ R) := by
  sorry

end Parcours.Logique

#verifier
