/- @parcours
celebre: 51
titre: Le théorème de Wilson
difficulte: 5
genre: boss
solution: non
requiert: Arithmetique.Bezout, Arithmetique.Congruences
indice: Idée : dans `{1, …, p-1}`, chaque élément `a` a un inverse modulo `p` (Bézout). Seuls `1` et `p-1` sont leurs propres inverses (car `a² ≡ 1` donne `p ∣ (a-1)(a+1)`).
indice: Les autres se regroupent par paires `{a, a⁻¹}` dont le produit vaut 1 modulo `p`. Il reste `1 × (p-1) ≡ -1`.
indice: Formaliser les « paires » est le vrai défi. Une approche : récurrence sur des listes d'éléments stables par inversion, ou travailler avec `List.range` et des permutations.
-/
import Solutions.Arithmetique.LemmeEuclide

/-!
# 💀 Le théorème de Wilson

> `p` est premier si et seulement si `(p-1)! ≡ -1 (mod p)`.

On demande le sens direct : pour `p` premier, `p` divise `(p-1)! + 1`.
Énoncé par Wilson en 1770, prouvé par Lagrange en 1771.

C'est un **boss** : pas de solution de référence. L'arithmétique est facile sur papier, mais
formaliser le regroupement par paires « élément × inverse » demande de l'organisation.

## À prouver
`wilson (hp : Premier p) : p ∣ Parcours.Recurrence.fact (p - 1) + 1`

## Ressources
- [Théorème de Wilson (Wikipédia)](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_de_Wilson)
-/

namespace Parcours.Arith

theorem wilson {p : Nat} (hp : Premier p) : p ∣ Parcours.Recurrence.fact (p - 1) + 1 := by -- @exo
  sorry

end Parcours.Arith

#verifier
