/- @parcours
titre: Le théorème des McNuggets
difficulte: 3
requiert: Enigmes.Timbres
indice: `pas_43` : `omega` explore tout seul.
indice: `a_partir_de_44` : récurrence forte (`induction n using Nat.strongRecOn`). Si `n ≥ 50`, utilise `n − 6` ; sinon, donne les six décompositions à la main (44 = 6 + 18 + 20…).
-/
import Solutions.Recurrence.Definitions

/-!
# Le théorème des McNuggets

Les McNuggets étaient vendus par boîtes de 6, 9 et 20. Quel est le plus grand nombre de nuggets
qu'on ne peut **pas** commander exactement ? Réponse : **43**. Tout nombre à partir de 44 est
possible.

## Se le représenter
Si on sait faire 44, 45, 46, 47, 48 et 49 (six nombres consécutifs), on sait faire tous les
suivants en ajoutant des boîtes de 6.

## À prouver
1. `pas_43 : ¬ Commande 43`
2. `a_partir_de_44 : 44 ≤ n → Commande n`

## Ressources
- [Nombre de McNugget (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Coin_problem#McNugget_numbers)
-/

namespace Parcours.Enigmes

def Commande (n : Nat) : Prop := ∃ a b c, n = 6 * a + 9 * b + 20 * c

theorem pas_43 : ¬ Commande 43 := by -- @exo
  rintro ⟨a, b, c, h⟩
  omega

theorem a_partir_de_44 : ∀ n, 44 ≤ n → Commande n := by -- @exo
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro h
    by_cases h' : 50 ≤ n
    · obtain ⟨a, b, c, e⟩ := ih (n - 6) (by omega) (by omega)
      exact ⟨a + 1, b, c, by omega⟩
    · have : n = 44 ∨ n = 45 ∨ n = 46 ∨ n = 47 ∨ n = 48 ∨ n = 49 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨1, 2, 1, rfl⟩
      · exact ⟨0, 5, 0, rfl⟩
      · exact ⟨1, 0, 2, rfl⟩
      · exact ⟨0, 3, 1, rfl⟩
      · exact ⟨8, 0, 0, rfl⟩
      · exact ⟨0, 1, 2, rfl⟩

end Parcours.Enigmes

#verifier
