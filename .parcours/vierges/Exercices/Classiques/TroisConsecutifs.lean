import Exercices.Arithmetique.Definitions

/-!
# Trois entiers consécutifs

## Se le représenter
Parmi trois entiers consécutifs, il y a un multiple de 2 et un multiple de 3 : leur produit est
divisible par 6.

## À prouver
`trois_consecutifs (n : Nat) : (n * (n + 1) * (n + 2)) % 6 = 0`

---
*Exercice* `Classiques.TroisConsecutifs` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Classiques.TroisConsecutifs` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem trois_consecutifs (n : Nat) : (n * (n + 1) * (n + 2)) % 6 = 0 := by
  sorry

end Parcours.Classiques

#verifier
