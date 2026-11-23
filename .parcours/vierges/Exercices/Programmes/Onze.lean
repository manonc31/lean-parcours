import Exercices.Programmes.Definitions

/-!
# La règle de divisibilité par 11

Pour savoir si un nombre est divisible par 11, on fait la somme **alternée** de ses chiffres en
partant des unités : `918082 → 2 − 8 + 0 − 8 + 1 − 9 = −22`, divisible par 11, donc 918082 aussi.
Pourquoi ? Parce que `10 ≡ −1 (mod 11)`.

## À prouver
1. `onze_alterne : (n - alterne n) % 11 = 0` (dans `Int`)
2. `onze_divise : n % 11 = 0 ↔ alterne n % 11 = 0`

---
*Exercice* `Programmes.Onze` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Programmes.Onze` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

def alterne (n : Nat) : Int := if n < 10 then n else ((n % 10 : Nat) : Int) - alterne (n / 10)
termination_by n
decreasing_by omega

theorem onze_alterne (n : Nat) : ((n : Int) - alterne n) % 11 = 0 := by
  sorry

theorem onze_divise (n : Nat) : n % 11 = 0 ↔ alterne n % 11 = 0 := by
  sorry

end Parcours.Prog

#verifier
