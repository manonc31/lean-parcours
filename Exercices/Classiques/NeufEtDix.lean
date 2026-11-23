import Exercices.Arithmetique.Definitions

/-!
# Pourquoi la preuve par neuf marche

## Se le représenter
`10 = 9 + 1` : toutes les puissances de 10 valent 1 modulo 9. Donc `abc = 100a + 10b + c ≡ a + b + c`.
C'est le secret de la preuve par neuf.

## À prouver
`dix_mod_neuf (n : Nat) : (10 ^ n) % 9 = 1`

---
*Exercice* `Classiques.NeufEtDix` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Classiques.NeufEtDix` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

open Parcours.Recurrence

theorem dix_mod_neuf (n : Nat) : (10 ^ n) % 9 = 1 := by
  sorry

end Parcours.Classiques

#verifier
