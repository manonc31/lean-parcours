import Exercices.Recurrence.Definitions

/-!
# Une somme pondérée

`Σ k·2ᵏ` pour `k` de 0 à `n` vaut `(n − 1)·2ⁿ⁺¹ + 2`. Pour éviter la soustraction, on écrit :
`Σ k·2ᵏ + 2ⁿ⁺¹ = n·2ⁿ⁺¹ + 2`.

## À prouver
`somme_ponderee (n : Nat) : somme (fun k => k * 2 ^ k) (n + 1) + 2 ^ (n + 1) = n * 2 ^ (n + 1) + 2`

---
*Exercice* `Recurrence.SommePuissancesPonderees` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Recurrence.SommePuissancesPonderees` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Recurrence

theorem somme_ponderee (n : Nat) :
    somme (fun k => k * 2 ^ k) (n + 1) + 2 ^ (n + 1) = n * 2 ^ (n + 1) + 2 := by
  sorry

end Parcours.Recurrence

#verifier
