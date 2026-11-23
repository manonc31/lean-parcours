import Exercices.Arithmetique.Definitions

/-!
# Le théorème de Wilson, vérifié

Le théorème de Wilson (1770) : `p` est premier si et seulement si `(p − 1)! + 1` est divisible par
`p`. C'est un test de primalité parfait… mais inutilisable en pratique (calculer `(p − 1)!` est
bien trop long). Vérifions-le pour les petits nombres.

## À prouver
`wilson_petits : ∀ p < 40, 2 ≤ p → ((fact (p - 1) + 1) % p = 0 ↔ estPremierB p = true)`

## Ressources
- [Théorème de Wilson (Wikipédia)](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_de_Wilson)

---
*Exercice* `Arithmetique.WilsonPetits` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Arithmetique.WilsonPetits` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Arith

open Parcours.Recurrence

def estPremierB (p : Nat) : Bool := 2 ≤ p && (List.range p).all fun d => d < 2 || p % d != 0

theorem wilson_petits : ∀ p, p < 40 → 2 ≤ p → ((fact (p - 1) + 1) % p = 0 ↔ estPremierB p = true) := by
  sorry

end Parcours.Arith

#verifier
