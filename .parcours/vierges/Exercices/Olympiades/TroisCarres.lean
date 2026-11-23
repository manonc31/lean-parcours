import Exercices.Arithmetique.Definitions

/-!
# Trois divise une somme de deux carrés

Si `3` divise `a² + b²`, alors `3` divise `a` et `b`. Les carrés modulo 3 valent 0 ou 1 :
pour que la somme fasse 0, il faut deux 0.

## À prouver
`trois_divise_carres : (a * a + b * b) % 3 = 0 → a % 3 = 0 ∧ b % 3 = 0`

---
*Exercice* `Olympiades.TroisCarres` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Olympiades.TroisCarres` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Olymp

theorem trois_divise_carres (a b : Nat) (h : (a * a + b * b) % 3 = 0) : a % 3 = 0 ∧ b % 3 = 0 := by
  sorry

end Parcours.Olymp

#verifier
