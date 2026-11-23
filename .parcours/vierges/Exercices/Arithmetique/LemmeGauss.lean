import Exercices.Arithmetique.PgcdMul

/-!
# Le lemme de Gauss

> Si `a` divise `b·c` et que `a` est premier avec `b`, alors `a` divise `c`.

## À prouver
`lemme_gauss : a ∣ b * c → pgcd a b = 1 → a ∣ c`

## Ressources
- [Lemme de Gauss (Wikipédia)](https://fr.wikipedia.org/wiki/Lemme_de_Gauss)

---
*Exercice* `Arithmetique.LemmeGauss` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Arithmetique.LemmeGauss` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Arith

theorem lemme_gauss {a b c : Nat} (h : a ∣ b * c) (hab : pgcd a b = 1) : a ∣ c := by
  sorry

end Parcours.Arith

#verifier
