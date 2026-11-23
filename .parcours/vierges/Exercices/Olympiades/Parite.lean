import Exercices.Arithmetique.Definitions

/-!
# Échauffement de compétition

Trois classiques des compétitions, tous résolus par la même technique : **raisonner selon le
reste** de `n` dans une division, et calculer modulo.

## À prouver
1. `produit_consecutifs : (n * (n + 1)) % 2 = 0` (le produit de deux entiers consécutifs est pair)
2. `carre_mod_trois : (n * n) % 3 ≠ 2` (un carré n'est jamais de la forme `3k + 2`)
3. `cube_mod_six : (n * n * n) % 6 = n % 6` (donc 6 divise `n³ − n`)

---
*Exercice* `Olympiades.Parite` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Olympiades.Parite` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Olymp

theorem produit_consecutifs (n : Nat) : (n * (n + 1)) % 2 = 0 := by
  sorry

theorem carre_mod_trois (n : Nat) : (n * n) % 3 ≠ 2 := by
  sorry

theorem cube_mod_six (n : Nat) : (n * n * n) % 6 = n % 6 := by
  sorry

end Parcours.Olymp

#verifier
