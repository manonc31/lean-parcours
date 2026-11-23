import Exercices.Arithmetique.Definitions

/-!
# n² + 3n + 5 et 121

Un classique des olympiades : `n² + 3n + 5` n'est **jamais** divisible par 121.

## Se le représenter
`4(n² + 3n + 5) = (2n + 3)² + 11`. Si 121 divisait le membre de gauche, 11 diviserait `(2n+3)²`,
donc `2n + 3`, donc 121 diviserait `(2n+3)²`… et donc 11 : absurde.

En Lean, on peut aussi écrire `n = 121q + r` et vérifier les 121 restes.

## À prouver
`jamais_121 : (n * n + 3 * n + 5) % 121 ≠ 0`

---
*Exercice* `Olympiades.Jamais121` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Olympiades.Jamais121` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Olymp

theorem jamais_121 (n : Nat) : (n * n + 3 * n + 5) % 121 ≠ 0 := by
  sorry

end Parcours.Olymp

#verifier
