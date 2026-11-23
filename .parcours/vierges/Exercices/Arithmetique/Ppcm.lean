import Exercices.Arithmetique.PgcdDivise

/-!
# Le PPCM

Le plus petit commun multiple : `ppcm a b = a × b / pgcd a b`. (Les lemmes de division de `Nat`
sont permis : `Nat.mul_div_cancel'`, `Nat.mul_div_assoc`.)

## À prouver
1. `pgcd_mul_ppcm : pgcd a b * ppcm a b = a * b`
2. `divise_ppcm : a ∣ ppcm a b`

---
*Exercice* `Arithmetique.Ppcm` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Arithmetique.Ppcm` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Arith

def ppcm (a b : Nat) : Nat := a * b / pgcd a b

theorem pgcd_mul_ppcm (a b : Nat) : pgcd a b * ppcm a b = a * b := by
  sorry

theorem divise_ppcm (a b : Nat) : a ∣ ppcm a b := by
  sorry

end Parcours.Arith

#verifier
