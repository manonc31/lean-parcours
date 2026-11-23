/- @parcours
celebre: 20
titre: Le théorème des deux carrés de Fermat
difficulte: 5
genre: boss
solution: non
requiert: Arithmetique.LemmeEuclide, Arithmetique.Wilson
indice: Preuve « en une phrase » de Zagier (1990) : l'involution sur `{(x, y, z) : x² + 4yz = p}` a exactement un point fixe, donc le nombre de solutions est impair, donc l'involution `(x, y, z) ↦ (x, z, y)` a un point fixe : `y = z`, et `p = x² + (2y)²`.
indice: Alternative : par Wilson, `((p-1)/2)!² ≡ -1 (mod p)` donc -1 est un carré mod p ; puis le lemme de Thue (principe des tiroirs).
-/
import Solutions.Arithmetique.LemmeEuclide

/-!
# 💀 Le théorème des deux carrés de Fermat

> Un nombre premier `p ≡ 1 (mod 4)` est somme de deux carrés.

`5 = 1 + 4`, `13 = 4 + 9`, `17 = 1 + 16`, `29 = 4 + 25`… Énoncé par Fermat dans une lettre de
Noël 1640 (« théorème de Noël »), prouvé par Euler un siècle plus tard. Don Zagier en a donné
une célèbre « preuve en une phrase » en 1990.

Boss sans solution de référence.

## À prouver
`deux_carres (hp : Premier p) (h : p % 4 = 1) : ∃ a b, p = a ^ 2 + b ^ 2`

## Ressources
- [Théorème des deux carrés de Fermat (Wikipédia)](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_des_deux_carr%C3%A9s_de_Fermat)
- [La preuve de Zagier (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Fermat%27s_theorem_on_sums_of_two_squares#Zagier's_%22one-sentence_proof%22)
-/

namespace Parcours.Arith

theorem deux_carres {p : Nat} (hp : Premier p) (h : p % 4 = 1) : ∃ a b, p = a ^ 2 + b ^ 2 := by -- @exo
  sorry

end Parcours.Arith

#verifier
