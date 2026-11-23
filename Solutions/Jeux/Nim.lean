/- @parcours
titre: Le jeu de Nim à un tas
difficulte: 3
requiert: Recurrence.Pieces
indice: Récurrence forte : `induction n using Nat.strongRecOn with | ind n ih => …`, puis `match n with | 0 | 1 | 2 | n + 3`.
indice: Les trois premiers cas se vérifient par calcul (`rfl`).
indice: Cas `n + 3` : `simp only [gagnante]`, puis remplace les trois appels avec `ih`. Il reste un calcul sur `n % 4` : `have : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega`, puis `rcases this with h | h | h | h <;> simp [h, Nat.add_mod]`.
-/
import Solutions.Recurrence.Definitions

/-!
# Le jeu de Nim à un tas

Il y a `n` allumettes. Chacun son tour, un joueur en retire 1, 2 ou 3. Celui qui prend la
**dernière** gagne. (Version popularisée par l'émission Fort Boyard !)

Une position est **gagnante** si le joueur dont c'est le tour peut forcer la victoire :
c'est le cas s'il existe un coup qui mène à une position **perdante** pour l'adversaire.

**Théorème** : les positions perdantes sont exactement les multiples de 4.
Stratégie : laisse toujours un multiple de 4 à ton adversaire !

## À prouver
`nim (n : Nat) : gagnante n = (n % 4 != 0)`

## Ressources
- [Jeu de Nim (Wikipédia)](https://fr.wikipedia.org/wiki/Jeux_de_Nim)
-/

namespace Parcours.Jeux

/-- `gagnante n` : avec `n` allumettes, le joueur qui doit jouer peut-il forcer la victoire ? -/
def gagnante : Nat → Bool
  | 0 => false
  | 1 => true
  | 2 => true
  | n + 3 => !gagnante (n + 2) || !gagnante (n + 1) || !gagnante n

theorem nim (n : Nat) : gagnante n = (n % 4 != 0) := by -- @exo
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | n + 3 =>
      simp only [gagnante]
      rw [ih (n + 2) (by omega), ih (n + 1) (by omega), ih n (by omega)]
      have : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
      rcases this with h | h | h | h <;> simp [h, Nat.add_mod]

end Parcours.Jeux

#verifier
