import Exercices.Recurrence.Definitions

/-!
# Le logarithme en base 2

`log2' n` = le nombre de fois qu'on peut diviser `n` par 2 avant de tomber sous 2.
C'est le nombre de chiffres binaires de `n`, moins 1. C'est aussi le nombre d'étapes d'une
recherche dichotomique dans un tableau de taille `n`.

## À prouver
1. `deux_pow_le : 1 ≤ n → 2 ^ log2' n ≤ n`
2. `lt_deux_pow_succ : n < 2 ^ (log2' n + 1)`

---
*Exercice* `Terminaison.Logarithme` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Terminaison.Logarithme` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Term

def log2' (n : Nat) : Nat :=
  if n < 2 then 0 else log2' (n / 2) + 1
termination_by n
decreasing_by omega

theorem deux_pow_le (n : Nat) (h : 1 ≤ n) : 2 ^ log2' n ≤ n := by
  sorry

theorem lt_deux_pow_succ (n : Nat) : n < 2 ^ (log2' n + 1) := by
  sorry

end Parcours.Term

#verifier
