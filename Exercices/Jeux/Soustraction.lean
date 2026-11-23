import Exercices.Recurrence.Definitions

/-!
# Le jeu de soustraction 1-3-4

Un tas de `n` jetons ; chacun son tour, on en retire 1, 3 ou 4. Celui qui ne peut plus jouer a
perdu. Qui gagne ? En calculant les premières positions, on voit apparaître un motif de période 7 :
les positions **perdantes** (pour celui qui doit jouer) sont celles où `n ≡ 0` ou `2 (mod 7)`.

Une position est gagnante s'il existe un coup qui mène à une position perdante.

## À prouver
`gagne134_spec : gagne134 n = true ↔ n % 7 ≠ 0 ∧ n % 7 ≠ 2`

## Ressources
- [Jeu de soustraction (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Subtraction_game)

---
*Exercice* `Jeux.Soustraction` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Jeux.Soustraction` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Jeux

def gagne134 (n : Nat) : Bool :=
  if h : n = 0 then false
  else !gagne134 (n - 1) || (3 ≤ n && !gagne134 (n - 3)) || (4 ≤ n && !gagne134 (n - 4))
termination_by n
decreasing_by all_goals omega

theorem gagne134_spec (n : Nat) : gagne134 n = true ↔ (n % 7 ≠ 0 ∧ n % 7 ≠ 2) := by
  sorry

end Parcours.Jeux

#verifier
