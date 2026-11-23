/- @parcours
titre: La racine numérique
difficulte: 3
requiert: Enigmes.PreuveParNeuf
indice: `sommeChiffres_le` : `fun_induction`, puis `omega`.
indice: Pour `racineNum_spec` : `fun_induction racineNum n` ; dans le cas récursif, `sommeChiffres n` et `n` ont le même reste modulo 9, et `sommeChiffres n > 0`.
-/
import Solutions.Programmes.Definitions
import Solutions.Enigmes.PreuveParNeuf

/-!
# La racine numérique

On additionne les chiffres d'un nombre, puis ceux du résultat, etc., jusqu'à obtenir un seul
chiffre : `9875 → 29 → 11 → 2`. C'est la **racine numérique**. Grâce à la preuve par neuf, on peut
la calculer d'un coup : c'est `1 + (n − 1) mod 9` (pour `n > 0`).

On réutilise `sommeChiffres` et `somme_chiffres_mod_neuf` de l'énigme « La preuve par neuf ».

## À prouver
1. `sommeChiffres_le`, `sommeChiffres_lt`, `sommeChiffres_pos` : de quoi justifier que le
   programme s'arrête.
2. `racineNum_spec : racineNum n = if n = 0 then 0 else 1 + (n - 1) % 9`

## Ressources
- [Racine numérique (Wikipédia)](https://fr.wikipedia.org/wiki/Racine_num%C3%A9rique)
-/

namespace Parcours.Prog

open Parcours.Enigmes

theorem sommeChiffres_le (n : Nat) : sommeChiffres n ≤ n := by -- @exo
  fun_induction sommeChiffres n <;> omega

theorem sommeChiffres_lt (n : Nat) (h : 10 ≤ n) : sommeChiffres n < n := by -- @exo
  rw [sommeChiffres]
  have := sommeChiffres_le (n / 10)
  split <;> omega

theorem sommeChiffres_pos (n : Nat) (h : 0 < n) : 0 < sommeChiffres n := by -- @exo
  fun_induction sommeChiffres n with
  | case1 n _ => exact h
  | case2 n h' ih =>
    by_cases h0 : n % 10 = 0
    · have := ih (by omega)
      omega
    · omega

def racineNum (n : Nat) : Nat := if h : n < 10 then n else racineNum (sommeChiffres n)
termination_by n
decreasing_by exact sommeChiffres_lt n (by omega)

theorem racineNum_spec (n : Nat) : racineNum n = if n = 0 then 0 else 1 + (n - 1) % 9 := by -- @exo
  fun_induction racineNum n with
  | case1 n h =>
    split <;> omega
  | case2 n h ih =>
    have h9 := somme_chiffres_mod_neuf n
    have hp := sommeChiffres_pos n (by omega)
    rw [ih]
    simp only [show sommeChiffres n ≠ 0 by omega, show n ≠ 0 by omega, ↓reduceIte]
    omega

end Parcours.Prog

#verifier
