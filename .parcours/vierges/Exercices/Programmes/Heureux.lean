import Exercices.Programmes.Definitions

/-!
# Les nombres heureux

Prends un nombre, remplace-le par la somme des carrés de ses chiffres, et recommence :
`7 → 49 → 97 → 130 → 10 → 1`. Si on arrive à 1, le nombre est **heureux**. Sinon, on tombe
toujours dans le même cycle : `4 → 16 → 37 → 58 → 89 → 145 → 42 → 20 → 4`.

## À prouver
1. `sept_heureux : repeter carresChiffres 5 7 = 1`
2. `cycle_malheureux : repeter carresChiffres 8 4 = 4`
3. `dix_neuf` : il y a 19 nombres heureux entre 1 et 99.
4. `toujours` : pour tout `0 < n < 1000`, après 20 étapes on est à 1 ou dans le cycle de 4.

## Ressources
- [Nombre heureux (Wikipédia)](https://fr.wikipedia.org/wiki/Nombre_heureux)

---
*Exercice* `Programmes.Heureux` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Programmes.Heureux` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

def carresChiffres (n : Nat) : Nat :=
  (n % 10) ^ 2 + (n / 10 % 10) ^ 2 + (n / 100 % 10) ^ 2 + (n / 1000 % 10) ^ 2

def cycle4 : List Nat := [4, 16, 37, 58, 89, 145, 42, 20]

theorem sept_heureux : repeter carresChiffres 5 7 = 1 := by
  sorry

theorem cycle_malheureux : repeter carresChiffres 8 4 = 4 := by
  sorry

theorem dix_neuf : ((List.range 100).filter fun n => 0 < n && repeter carresChiffres 20 n == 1).length = 19 := by
  sorry

theorem toujours : ∀ n, n < 1000 → 0 < n → repeter carresChiffres 20 n = 1 ∨ repeter carresChiffres 20 n ∈ cycle4 := by
  sorry

end Parcours.Prog

#verifier
