import Exercices.Arithmetique.PgcdDivise

/-!
# PGCD et multiplication

`pgcd (a·c) (b·c) = pgcd a b · c`. Ce petit lemme est la clé du lemme de Gauss.

## À prouver
`pgcd_mul_droite (a b c : Nat) : pgcd (a * c) (b * c) = pgcd a b * c`

---
*Exercice* `Arithmetique.PgcdMul` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Arithmetique.PgcdMul` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Arith

theorem pgcd_mul_droite (a b c : Nat) : pgcd (a * c) (b * c) = pgcd a b * c := by
  sorry

end Parcours.Arith

#verifier
