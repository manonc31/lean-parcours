import Exercices.Algorithmes.Definitions

/-!
# L'exponentiation rapide

Calculer `aⁿ` en multipliant `n` fois prend `n` étapes. L'exponentiation rapide utilise
`a^(2k) = (a²)^k` et `a^(2k+1) = a · (a²)^k` : seulement `log₂ n` étapes ! Pour `n` = 1 milliard,
c'est 30 multiplications au lieu d'un milliard. Utilisée partout en cryptographie (RSA).

## À prouver
`expRapide_eq (a n : Nat) : expRapide a n = a ^ n`

---
*Exercice* `Algorithmes.ExpRapide` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Algorithmes.ExpRapide` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Algo

def expRapide (a n : Nat) : Nat :=
  if n = 0 then 1
  else if n % 2 = 0 then expRapide (a * a) (n / 2)
  else a * expRapide (a * a) (n / 2)
termination_by n
decreasing_by all_goals omega

theorem expRapide_eq (a n : Nat) : expRapide a n = a ^ n := by
  sorry

end Parcours.Algo

#verifier
