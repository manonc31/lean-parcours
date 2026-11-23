import ParcoursOutils

/-!
# Le ou exclusif

« Ou bien P, ou bien Q, mais pas les deux » : le **ou exclusif** (XOR).

## À prouver
1. `oux_comm : OuX P Q → OuX Q P`
2. `oux_soi : ¬OuX P P`
3. `oux_faux : OuX P False ↔ P`

---
*Exercice* `Logique.OuExclusif` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Logique.OuExclusif` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Logique

def OuX (P Q : Prop) : Prop := (P ∨ Q) ∧ ¬(P ∧ Q)

theorem oux_comm {P Q : Prop} (h : OuX P Q) : OuX Q P := by
  sorry

theorem oux_soi (P : Prop) : ¬OuX P P := by
  sorry

theorem oux_faux (P : Prop) : OuX P False ↔ P := by
  sorry

end Parcours.Logique

#verifier
