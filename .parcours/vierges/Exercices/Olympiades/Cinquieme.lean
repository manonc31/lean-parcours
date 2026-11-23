import Exercices.Arithmetique.Definitions

/-!
# La puissance cinquième

Pour tout entier `n`, `n⁵` et `n` ont le même dernier chiffre ! (Essaie : `2⁵ = 32`, `3⁵ = 243`, `7⁵ = 16807`.)
Ici, la version modulo 5 (c'est le petit théorème de Fermat pour `p = 5`).

## À prouver
`cinquieme (n : Nat) : (n * n * n * n * n) % 5 = n % 5`

---
*Exercice* `Olympiades.Cinquieme` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Olympiades.Cinquieme` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Olymp

theorem cinquieme (n : Nat) : (n * n * n * n * n) % 5 = n % 5 := by
  sorry

end Parcours.Olymp

#verifier
