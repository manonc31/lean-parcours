/- @parcours
titre: Le menteur 561
difficulte: 2
requiert: Informatique.RSA
indice: Un calcul : `decide +kernel` (avec l'exponentiation rapide de « RSA en miniature »).
indice: Pourquoi ? 560 est multiple de `2`, `10` et `16`, c'est-à-dire de `3 − 1`, `11 − 1` et `17 − 1` (critère de Korselt).
-/
import Solutions.Informatique.RSA

/-!
# Le menteur 561

Le petit théorème de Fermat dit : si `p` est premier, alors `aᵖ⁻¹ ≡ 1 (mod p)` pour tout `a` non
multiple de `p`. La réciproque est **fausse** ! `561 = 3 × 11 × 17` n'est pas premier, mais
`a⁵⁶⁰ ≡ 1 (mod 561)` pour **tous** les `a` premiers avec 561. C'est le plus petit **nombre de
Carmichael** (1910). Les tests de primalité modernes (Miller-Rabin) doivent déjouer ces menteurs.

## À prouver
1. `compose : 561 = 3 * 11 * 17`
2. `menteur` : pour tout `a < 561` premier avec 561, `a⁵⁶⁰ mod 561 = 1`.

## Ressources
- [Nombre de Carmichael (Wikipédia)](https://fr.wikipedia.org/wiki/Nombre_de_Carmichael)
-/

namespace Parcours.Arith

open Parcours.Info

theorem compose : 561 = 3 * 11 * 17 := by -- @exo
  decide

theorem menteur : ∀ a, a < 561 → a % 3 ≠ 0 → a % 11 ≠ 0 → a % 17 ≠ 0 →
    puissMod 20 a 560 561 = 1 := by -- @exo
  decide +kernel

end Parcours.Arith

#verifier
