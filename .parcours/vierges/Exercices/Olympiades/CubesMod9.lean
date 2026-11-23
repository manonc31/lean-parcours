import Exercices.Arithmetique.Definitions

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

---
*Exercice* `Olympiades.CubesMod9` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Olympiades.CubesMod9` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Olymp

theorem cube_mod_neuf (n : Nat) : n ^ 3 % 9 = 0 ∨ n ^ 3 % 9 = 1 ∨ n ^ 3 % 9 = 8 := by
  sorry

theorem pas_quatre (x y z : Nat) : (x ^ 3 + y ^ 3 + z ^ 3) % 9 ≠ 4 := by
  sorry

end Parcours.Olymp

#verifier
