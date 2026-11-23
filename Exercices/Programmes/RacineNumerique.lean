import Exercices.Programmes.Definitions
import Exercices.Enigmes.PreuveParNeuf

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

---
*Exercice* `Programmes.RacineNumerique` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Programmes.RacineNumerique` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

open Parcours.Enigmes

theorem sommeChiffres_le (n : Nat) : sommeChiffres n ≤ n := by
  sorry

theorem sommeChiffres_lt (n : Nat) (h : 10 ≤ n) : sommeChiffres n < n := by
  sorry

theorem sommeChiffres_pos (n : Nat) (h : 0 < n) : 0 < sommeChiffres n := by
  sorry

def racineNum (n : Nat) : Nat := if h : n < 10 then n else racineNum (sommeChiffres n)
termination_by n
decreasing_by exact sommeChiffres_lt n (by omega)

theorem racineNum_spec (n : Nat) : racineNum n = if n = 0 then 0 else 1 + (n - 1) % 9 := by
  sorry

end Parcours.Prog

#verifier
