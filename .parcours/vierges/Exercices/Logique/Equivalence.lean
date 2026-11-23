import Exercices.Logique.Et
import Exercices.Logique.Ou

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

---
*Exercice* `Logique.Equivalence` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Logique.Equivalence` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Logique

variable {P Q R : Prop}

theorem equiv_refl : P ↔ P := by
  sorry

theorem equiv_symm (h : P ↔ Q) : Q ↔ P := by
  sorry

theorem equiv_trans (h1 : P ↔ Q) (h2 : Q ↔ R) : P ↔ R := by
  sorry

theorem et_comm_iff : P ∧ Q ↔ Q ∧ P := by
  sorry

theorem ou_comm_iff : P ∨ Q ↔ Q ∨ P := by
  sorry

end Parcours.Logique

#verifier
