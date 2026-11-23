/- @parcours
celebre: 85
titre: La preuve par neuf
difficulte: 3
requiert: Arithmetique.Congruences
indice: `fun_induction sommeChiffres n with` : un cas `n < 10` et un cas récursif.
indice: Cas récursif : `n = 10 * (n / 10) + n % 10`, et `10 ≡ 1 (mod 9)`. Avec `ih : sommeChiffres (n / 10) % 9 = (n / 10) % 9`, `omega` conclut (il connaît `/` et `%` par des constantes).
indice: Pour 3 : `n % 3 = (n % 9) % 3` (car 3 divise 9) : `omega`.
-/
import Solutions.Arithmetique.Definitions

/-!
# La preuve par neuf

Un nombre et la somme de ses chiffres ont le même reste dans la division par 9 (et par 3).
D'où la règle : « un nombre est divisible par 9 si et seulement si la somme de ses chiffres l'est ».
C'est aussi la vieille « preuve par neuf » pour vérifier les multiplications à la main.

## À prouver
1. `somme_chiffres_mod_neuf : sommeChiffres n % 9 = n % 9`
2. `divisible_par_trois : n % 3 = 0 ↔ sommeChiffres n % 3 = 0`

## Ressources
- [Preuve par neuf (Wikipédia)](https://fr.wikipedia.org/wiki/Preuve_par_neuf)
-/

namespace Parcours.Enigmes

def sommeChiffres (n : Nat) : Nat :=
  if n < 10 then n else sommeChiffres (n / 10) + n % 10
termination_by n
decreasing_by omega

theorem somme_chiffres_mod_neuf (n : Nat) : sommeChiffres n % 9 = n % 9 := by -- @exo
  fun_induction sommeChiffres n with
  | case1 n _ => rfl
  | case2 n _ ih => omega

theorem divisible_par_trois (n : Nat) : n % 3 = 0 ↔ sommeChiffres n % 3 = 0 := by -- @exo
  have h := somme_chiffres_mod_neuf n
  omega

end Parcours.Enigmes

#verifier
