import Exercices.Arithmetique.Definitions

/-!
# Trois chaussettes

## Se le représenter
Dans un tiroir de chaussettes noires et blanches, il suffit d'en prendre **trois** pour avoir une paire
de la même couleur. Version nombres : parmi trois entiers, deux ont la même parité.

## À prouver
`trois_chaussettes (a b c : Nat) : a % 2 = b % 2 ∨ b % 2 = c % 2 ∨ a % 2 = c % 2`

---
*Exercice* `Classiques.TroisChaussettes` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Classiques.TroisChaussettes` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem trois_chaussettes (a b c : Nat) : a % 2 = b % 2 ∨ b % 2 = c % 2 ∨ a % 2 = c % 2 := by
  sorry

end Parcours.Classiques

#verifier
