import Exercices.Arithmetique.Definitions

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

---
*Exercice* `Enigmes.PreuveParNeuf` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Enigmes.PreuveParNeuf` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Enigmes

def sommeChiffres (n : Nat) : Nat :=
  if n < 10 then n else sommeChiffres (n / 10) + n % 10
termination_by n
decreasing_by omega

theorem somme_chiffres_mod_neuf (n : Nat) : sommeChiffres n % 9 = n % 9 := by
  sorry

theorem divisible_par_trois (n : Nat) : n % 3 = 0 ↔ sommeChiffres n % 3 = 0 := by
  sorry

end Parcours.Enigmes

#verifier
