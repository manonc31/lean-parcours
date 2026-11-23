import Exercices.Arithmetique.Bezout

/-!
# Le théorème des restes chinois

> « Il y a des objets dont on ignore le nombre. Comptés 3 par 3, il en reste 2 ; 5 par 5, il en
> reste 3 ; 7 par 7, il en reste 2. Combien sont-ils ? » — Sun Zi, IIIᵉ siècle.

Si `m` et `n` sont premiers entre eux, on peut toujours trouver `x` ayant un reste imposé
modulo `m` ET un reste imposé modulo `n`. On travaille dans `Int` (`%` y est le reste positif).

## À prouver
`restes_chinois (h : pgcd m n = 1) (a b : Int) : ∃ x : Int, x % m = a % m ∧ x % n = b % n`

## Ressources
- [Théorème des restes chinois (Wikipédia)](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_des_restes_chinois)

---
*Exercice* `Arithmetique.RestesChinois` · difficulté ★★★★☆

💡 Indices : `./parcours indice Arithmetique.RestesChinois` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Arith

theorem restes_chinois {m n : Nat} (h : pgcd m n = 1) (a b : Int) :
    ∃ x : Int, x % m = a % m ∧ x % n = b % n := by
  sorry

end Parcours.Arith

#verifier
