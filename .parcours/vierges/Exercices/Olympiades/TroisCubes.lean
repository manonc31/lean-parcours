import Exercices.Classiques.Divisible3

/-!
# Trois cubes consécutifs

La somme de trois cubes consécutifs est toujours divisible par 9 : `1 + 8 + 27 = 36`,
`8 + 27 + 64 = 99`, `27 + 64 + 125 = 216`…

## Se le représenter
En développant : `n³ + (n+1)³ + (n+2)³ = 3(n³ + 2n) + 9(n² + n + 1)`. Et tu sais déjà que
`n³ + 2n` est divisible par 3 !

## À prouver
`trois_cubes : (n ^ 3 + (n + 1) ^ 3 + (n + 2) ^ 3) % 9 = 0`

---
*Exercice* `Olympiades.TroisCubes` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Olympiades.TroisCubes` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Olymp

theorem trois_cubes (n : Nat) : (n ^ 3 + (n + 1) ^ 3 + (n + 2) ^ 3) % 9 = 0 := by
  sorry

end Parcours.Olymp

#verifier
