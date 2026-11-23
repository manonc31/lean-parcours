import Exercices.Arithmetique.PgcdDivise

/-!
# L'identité de Bézout

Il existe des entiers **relatifs** `x` et `y` tels que `pgcd a b = a·x + b·y`.
On les calcule avec l'algorithme d'Euclide **étendu**.

Ici on travaille dans `Int` (les entiers relatifs de Lean). `(n : Int)` convertit un `Nat`.

## À prouver
`bezout (a b : Nat) : ∃ x y : Int, (pgcd a b : Int) = a * x + b * y`

## Ressources
- [Théorème de Bachet-Bézout (Wikipédia)](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_de_Bachet-B%C3%A9zout)

---
*Exercice* `Arithmetique.Bezout` · difficulté ★★★★☆

💡 Indices : `./parcours indice Arithmetique.Bezout` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Arith

theorem bezout (a b : Nat) : ∃ x y : Int, (pgcd a b : Int) = a * x + b * y := by
  sorry

end Parcours.Arith

#verifier
