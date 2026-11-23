/- @parcours
celebre: 7
titre: La loi de réciprocité quadratique
difficulte: 5
genre: boss
solution: non
requiert: Arithmetique.Wilson, Arithmetique.RestesChinois
indice: Étape 1 : critère d'Euler : `a` (non multiple de `p`) est un carré mod `p` ssi `a^((p-1)/2) ≡ 1 (mod p)`.
indice: Étape 2 : lemme de Gauss (le « lemme de Gauss » des résidus quadratiques, pas celui de la divisibilité) : compter les `a·k mod p` qui dépassent `p/2`.
indice: Étape 3 : le lemme d'Eisenstein et un comptage de points entiers sous la diagonale d'un rectangle `p/2 × q/2`.
indice: Ce boss est un vrai projet : prévois des dizaines de lemmes intermédiaires. Gauss en a donné 8 preuves différentes !
-/
import Solutions.Arithmetique.LemmeEuclide

/-!
# 💀 La loi de réciprocité quadratique

Le « théorème d'or » de Gauss (1796). Pour deux nombres premiers impairs distincts `p` et `q` :
`p` est un carré modulo `q` **et** `q` est un carré modulo `p`, ou bien aucun des deux…
**sauf** si `p ≡ q ≡ 3 (mod 4)`, auquel cas exactement un des deux l'est.

`EstCarre a p` : il existe `x` avec `x² ≡ a (mod p)`.

Boss sans solution de référence. Probablement l'exercice le plus dur du parcours
(hors problèmes ouverts) : il a fallu à Gauss un an de travail.

## À prouver
`reciprocite (hp : Premier p) (hq : Premier q) (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q) :
  (EstCarre p q ↔ EstCarre q p) ↔ (p % 4 = 1 ∨ q % 4 = 1)`

## Ressources
- [Loi de réciprocité quadratique (Wikipédia)](https://fr.wikipedia.org/wiki/Loi_de_r%C3%A9ciprocit%C3%A9_quadratique)
-/

namespace Parcours.Arith

/-- `a` est un carré modulo `p`. -/
def EstCarre (a p : Nat) : Prop := ∃ x, (x * x) % p = a % p

theorem reciprocite {p q : Nat} (hp : Premier p) (hq : Premier q) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hpq : p ≠ q) : (EstCarre p q ↔ EstCarre q p) ↔ (p % 4 = 1 ∨ q % 4 = 1) := by -- @exo
  sorry

end Parcours.Arith

#verifier
