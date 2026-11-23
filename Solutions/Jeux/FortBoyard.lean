/- @parcours
titre: Les bâtonnets de Fort Boyard
difficulte: 3
requiert: Jeux.Nim
indice: Même méthode que pour le Nim à un tas : récurrence forte, trois cas de base, puis un calcul modulo 4.
-/
import Solutions.Recurrence.Definitions

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
-/

namespace Parcours.Jeux

def gagnanteMisere : Nat → Bool
  | 0 => true
  | 1 => false
  | 2 => true
  | n + 3 => !gagnanteMisere (n + 2) || !gagnanteMisere (n + 1) || !gagnanteMisere n

theorem fort_boyard (n : Nat) : gagnanteMisere n = (n % 4 != 1) := by -- @exo
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | n + 3 =>
      simp only [gagnanteMisere]
      rw [ih (n + 2) (by omega), ih (n + 1) (by omega), ih n (by omega)]
      have : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
      rcases this with h | h | h | h <;> simp [h, Nat.add_mod]

end Parcours.Jeux

#verifier
