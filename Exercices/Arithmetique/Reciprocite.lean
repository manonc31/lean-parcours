import Exercices.Arithmetique.LemmeEuclide

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

---
*Exercice* `Arithmetique.Reciprocite` · difficulté ★★★★★

💡 Indices : `./parcours indice Arithmetique.Reciprocite` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Arith

/-- `a` est un carré modulo `p`. -/
def EstCarre (a p : Nat) : Prop := ∃ x, (x * x) % p = a % p

theorem reciprocite {p q : Nat} (hp : Premier p) (hq : Premier q) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hpq : p ≠ q) : (EstCarre p q ↔ EstCarre q p) ↔ (p % 4 = 1 ∨ q % 4 = 1) := by
  sorry

end Parcours.Arith

#verifier
