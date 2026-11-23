import Exercices.Arithmetique.Definitions

/-!
# Somme de trois cubes

Si `a + b + c = 0`, alors `a³ + b³ + c³ = 3abc`. Une identité qui sert souvent en compétition
(par exemple pour factoriser).

## À prouver
`somme_cubes (a b c : Int) (h : a + b + c = 0) : a ^ 3 + b ^ 3 + c ^ 3 = 3 * a * b * c`

---
*Exercice* `Olympiades.SommeCubes` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Olympiades.SommeCubes` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Olymp

theorem somme_cubes (a b c : Int) (h : a + b + c = 0) : a ^ 3 + b ^ 3 + c ^ 3 = 3 * a * b * c := by
  sorry

end Parcours.Olymp

#verifier
