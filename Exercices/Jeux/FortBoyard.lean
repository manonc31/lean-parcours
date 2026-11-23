import Exercices.Recurrence.Definitions

/-!
# Les bâtonnets de Fort Boyard

À Fort Boyard, on retire 1, 2 ou 3 bâtonnets, et celui qui prend le **dernier** a **perdu** (version
« misère » du Nim). Les positions perdantes deviennent celles où le nombre de bâtonnets vaut 1 modulo 4.
Le maître du temps laisse donc toujours `4k + 1` bâtonnets à son adversaire…

`gagnanteMisere n` : avec `n` bâtonnets, le joueur au trait peut-il forcer la victoire ?
(Avec 0 bâtonnet, l'adversaire vient de prendre le dernier : il a perdu, on a gagné.)

## À prouver
`fort_boyard (n : Nat) : gagnanteMisere n = (n % 4 != 1)`

## Ressources
- [Fort Boyard, les bâtonnets (Wikipédia)](https://fr.wikipedia.org/wiki/Jeux_de_Nim)

---
*Exercice* `Jeux.FortBoyard` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Jeux.FortBoyard` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Jeux

def gagnanteMisere : Nat → Bool
  | 0 => true
  | 1 => false
  | 2 => true
  | n + 3 => !gagnanteMisere (n + 2) || !gagnanteMisere (n + 1) || !gagnanteMisere n

theorem fort_boyard (n : Nat) : gagnanteMisere n = (n % 4 != 1) := by
  sorry

end Parcours.Jeux

#verifier
