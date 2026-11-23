/- @parcours
titre: Des bidons impossibles
difficulte: 3
requiert: Enigmes.Bidons
indice: Récurrence sur `h : Accessible 6 9 e` (`induction h`).
indice: Dans le cas `coup`, `e'` est l'un des 6 états de `suivants` : `simp only [suivants, List.mem_cons, …] at h` puis `rcases h with rfl | rfl | …`.
indice: `omega` connaît `min` et `%`.
-/
import Solutions.Enigmes.Bidons

/-!
# Des bidons impossibles

Avec un bidon de 6 litres et un bidon de 9 litres, peut-on obtenir 4 litres ? Non ! Quoi qu'on
fasse, chaque bidon contient toujours un **multiple de 3** litres : c'est un **invariant**.
(En général, on obtient exactement les multiples du PGCD des deux capacités.)

`Accessible A B e` : l'état `e` peut être atteint depuis `(0, 0)`.

## À prouver
1. `invariant : Accessible 6 9 e → e.1 % 3 = 0 ∧ e.2 % 3 = 0`
2. `jamais_quatre : Accessible 6 9 e → e.1 ≠ 4 ∧ e.2 ≠ 4`
-/

namespace Parcours.Enigmes

inductive Accessible (A B : Nat) : Contenu → Prop
  | depart : Accessible A B (0, 0)
  | coup {e e' : Contenu} : Accessible A B e → e' ∈ suivants A B e → Accessible A B e'

theorem invariant (e : Contenu) (h : Accessible 6 9 e) : e.1 % 3 = 0 ∧ e.2 % 3 = 0 := by -- @exo
  induction h with
  | depart => decide
  | coup _ h ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [suivants, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; omega)

theorem jamais_quatre (e : Contenu) (h : Accessible 6 9 e) : e.1 ≠ 4 ∧ e.2 ≠ 4 := by -- @exo
  have := invariant e h
  omega

end Parcours.Enigmes

#verifier
