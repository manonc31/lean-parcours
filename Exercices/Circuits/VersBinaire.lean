import Exercices.Circuits.Definitions

/-!
# Écrire un nombre en binaire

L'algorithme : le dernier bit est le reste de la division par 2, et on recommence avec le quotient.
Prouve que c'est correct : relire le nombre binaire redonne le nombre de départ.

## À prouver
`valeur_binaire : valeur (binaire n) = n`

---
*Exercice* `Circuits.VersBinaire` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Circuits.VersBinaire` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Circuits

def binaire (n : Nat) : List Bool :=
  if n = 0 then [] else (n % 2 == 1) :: binaire (n / 2)
termination_by n
decreasing_by omega

-- Essaie : `#eval binaire 6` affiche `[false, true, true]` (6 = 0 + 2 + 4).

theorem valeur_binaire (n : Nat) : valeur (binaire n) = n := by
  sorry

end Parcours.Circuits

#verifier
