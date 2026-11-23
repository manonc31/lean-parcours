import Exercices.Programmes.Definitions

/-!
# L'exponentiation modulaire

Pour calculer `a^n mod m` avec des nombres géants (c'est le cœur de RSA), on ne calcule jamais
`a^n` : on réduit modulo `m` à chaque étape, et on utilise `a^(2k) = (a^k)²`.

## À prouver
`expMod_spec : expMod a n m = a ^ n % m`

## Ressources
- [Exponentiation modulaire (Wikipédia)](https://fr.wikipedia.org/wiki/Exponentiation_modulaire)

---
*Exercice* `Programmes.ExpModulaire` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Programmes.ExpModulaire` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

def expMod (a n m : Nat) : Nat :=
  if n = 0 then 1 % m
  else if n % 2 = 0 then (expMod a (n / 2) m * expMod a (n / 2) m) % m
  else (expMod a (n / 2) m * expMod a (n / 2) m * a) % m
termination_by n
decreasing_by all_goals omega

theorem expMod_spec (a n m : Nat) : expMod a n m = a ^ n % m := by
  sorry

end Parcours.Prog

#verifier
