/- @parcours
titre: Les sommes de trois cubes
difficulte: 2
requiert: Olympiades.CinqTrente
indice: `Nat.pow_mod`, puis les 9 restes possibles avec `decide`.
indice: Pour la somme : `omega` combine les trois possibilités pour chaque cube.
-/
import Solutions.Arithmetique.Definitions

/-!
# Les sommes de trois cubes

Quels nombres sont sommes de trois cubes ? Un cube vaut toujours 0, 1 ou 8 modulo 9. Donc une
somme de trois cubes ne vaut jamais 4 ou 5 modulo 9 ! Par exemple, 4, 13, 22, 31… ne sont pas
sommes de trois cubes.

(Pour les autres, c'est un problème célèbre : avec des entiers négatifs autorisés, on n'a trouvé
une décomposition de 42 qu'en 2019, avec des nombres de 17 chiffres et un calcul géant !)

## À prouver
1. `cube_mod_neuf : n ^ 3 % 9 = 0 ∨ n ^ 3 % 9 = 1 ∨ n ^ 3 % 9 = 8`
2. `pas_quatre : (x ^ 3 + y ^ 3 + z ^ 3) % 9 ≠ 4`

## Ressources
- [Somme de trois cubes (Wikipédia)](https://fr.wikipedia.org/wiki/Somme_de_trois_cubes)
-/

namespace Parcours.Olymp

theorem cube_mod_neuf (n : Nat) : n ^ 3 % 9 = 0 ∨ n ^ 3 % 9 = 1 ∨ n ^ 3 % 9 = 8 := by -- @exo
  rw [Nat.pow_mod]
  have : n % 9 < 9 := Nat.mod_lt _ (by decide)
  generalize n % 9 = r at this ⊢
  revert r
  decide

theorem pas_quatre (x y z : Nat) : (x ^ 3 + y ^ 3 + z ^ 3) % 9 ≠ 4 := by -- @exo
  have hx := cube_mod_neuf x
  have hy := cube_mod_neuf y
  have hz := cube_mod_neuf z
  omega

end Parcours.Olymp

#verifier
