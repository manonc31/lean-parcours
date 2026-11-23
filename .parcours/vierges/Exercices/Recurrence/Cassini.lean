import Exercices.Recurrence.Definitions

/-!
# L'identité de Cassini

`F(n+2)·F(n) − F(n+1)² = (−1)ⁿ⁺¹`. Elle est derrière un célèbre « paradoxe » : un carré 8×8
découpé et réassemblé en rectangle 5×13… qui a une case de plus !

On travaille dans `Int` (les entiers relatifs de Lean) à cause du signe.

## À prouver
`cassini (n : Nat) : (fib (n + 2) : Int) * fib n - (fib (n + 1) : Int) ^ 2 = (-1) ^ (n + 1)`

## Ressources
- [Identité de Cassini (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Cassini_and_Catalan_identities)

---
*Exercice* `Recurrence.Cassini` · difficulté ★★★★☆

💡 Indices : `./parcours indice Recurrence.Cassini` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Recurrence

theorem cassini (n : Nat) :
    (fib (n + 2) : Int) * fib n - (fib (n + 1) : Int) ^ 2 = (-1) ^ (n + 1) := by
  sorry

end Parcours.Recurrence

#verifier
