import Exercices.Arithmetique.LemmeEuclide

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

---
*Exercice* `Arithmetique.DeuxCarres` · difficulté ★★★★★

💡 Indices : `./parcours indice Arithmetique.DeuxCarres` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Arith

theorem deux_carres {p : Nat} (hp : Premier p) (h : p % 4 = 1) : ∃ a b, p = a ^ 2 + b ^ 2 := by
  sorry

end Parcours.Arith

#verifier
