import Exercices.Arithmetique.Definitions

/-!
# n² + n + 1 n'est pas un carré

Pour `n ≥ 1`, `n² + n + 1` est coincé strictement entre deux carrés consécutifs :
`n² < n² + n + 1 < (n + 1)² = n² + 2n + 1`. Donc ce n'est pas un carré.

## À prouver
`pas_un_carre : 1 ≤ n → k * k ≠ n * n + n + 1`

---
*Exercice* `Olympiades.PasUnCarre` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Olympiades.PasUnCarre` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Olymp

theorem pas_un_carre (n k : Nat) (hn : 1 ≤ n) : k * k ≠ n * n + n + 1 := by
  sorry

end Parcours.Olymp

#verifier
