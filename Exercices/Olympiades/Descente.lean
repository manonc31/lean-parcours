import Exercices.Olympiades.TroisCarres

/-!
# La descente infinie

L'équation `x² + y² = 3z²` n'a que la solution `x = y = z = 0`.

## Se le représenter
C'est la **descente infinie** de Fermat : si `(x, y, z)` est une solution, alors 3 divise `x` et `y`
(exercice précédent), donc `9` divise `3z²`, donc 3 divise `z`, et `(x/3, y/3, z/3)` est une solution
**plus petite**. On ne peut pas descendre indéfiniment dans les entiers naturels : il faut que tout
soit nul.

En Lean, la descente infinie est une **récurrence forte** sur `z`.

## À prouver
`descente : x * x + y * y = 3 * (z * z) → x = 0 ∧ y = 0 ∧ z = 0`

## Ressources
- [Descente infinie (Wikipédia)](https://fr.wikipedia.org/wiki/Descente_infinie)

---
*Exercice* `Olympiades.Descente` · difficulté ★★★★☆

💡 Indices : `./parcours indice Olympiades.Descente` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Olymp

theorem descente : ∀ z x y : Nat, x * x + y * y = 3 * (z * z) → x = 0 ∧ y = 0 ∧ z = 0 := by
  sorry

end Parcours.Olymp

#verifier
