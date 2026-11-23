/- @parcours
titre: Le théorème des restes chinois
difficulte: 4
indice: Bézout donne `u v` avec `1 = m * u + n * v`. Essaie `x := a * n * v + b * m * u`.
indice: Modulo `m` : `x = a + m * (b * u - a * u)` (car `n * v = 1 - m * u`). Prouve cette égalité avec `grind`, puis `Int.add_mul_emod_self_left : (a + b * c) % b = a % b`.
indice: Pareil modulo `n`.
-/
import Solutions.Arithmetique.Bezout

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
-/

namespace Parcours.Arith

theorem restes_chinois {m n : Nat} (h : pgcd m n = 1) (a b : Int) :
    ∃ x : Int, x % m = a % m ∧ x % n = b % n := by -- @exo
  obtain ⟨u, v, huv⟩ := bezout m n
  rw [h] at huv
  refine ⟨a * n * v + b * m * u, ?_, ?_⟩
  · have e : a * n * v + b * m * u = a + m * (b * u - a * u) := by grind
    rw [e, Int.add_mul_emod_self_left]
  · have e : a * n * v + b * m * u = b + n * (a * v - b * v) := by grind
    rw [e, Int.add_mul_emod_self_left]

end Parcours.Arith

#verifier
