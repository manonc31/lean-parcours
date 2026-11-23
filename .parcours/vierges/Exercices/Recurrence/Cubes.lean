import Exercices.Recurrence.Gauss

/-!
# Le théorème de Nicomaque

`1³ + 2³ + ⋯ + n³ = (1 + 2 + ⋯ + n)²`. Une coïncidence magnifique, connue depuis l'Antiquité
(Nicomaque de Gérase, vers l'an 100).

## À prouver
`nicomaque (n : Nat) : somme (fun i => i ^ 3) (n + 1) = (somme (fun i => i) (n + 1)) ^ 2`

## Ressources
- [Théorème de Nicomaque (Wikipédia)](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_de_Nicomaque)

---
*Exercice* `Recurrence.Cubes` · difficulté ★★★★☆

💡 Indices : `./parcours indice Recurrence.Cubes` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Recurrence

theorem nicomaque (n : Nat) :
    somme (fun i => i ^ 3) (n + 1) = (somme (fun i => i) (n + 1)) ^ 2 := by
  sorry

end Parcours.Recurrence

#verifier
