import Exercices.Recurrence.Definitions

/-!
# L'inégalité de Bernoulli

`(1 + x)ⁿ ≥ 1 + n·x`. Simple, mais elle sert partout (convergence de suites, intérêts composés…).

## À prouver
`bernoulli (n x : Nat) : 1 + n * x ≤ (1 + x) ^ n`

## Ressources
- [Inégalité de Bernoulli (Wikipédia)](https://fr.wikipedia.org/wiki/In%C3%A9galit%C3%A9_de_Bernoulli)

---
*Exercice* `Recurrence.Bernoulli` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Recurrence.Bernoulli` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Recurrence

theorem bernoulli (n x : Nat) : 1 + n * x ≤ (1 + x) ^ n := by
  sorry

end Parcours.Recurrence

#verifier
