/- @parcours
titre: Le code de Gray
difficulte: 2
requiert: Circuits.Increment
indice: `longueur_gray` : récurrence ; `List.length_append`, `List.length_map`, `List.length_reverse`.
indice: `mots_gray` : un mot de `gray (n + 1)` est `false :: a` ou `true :: a` avec `a ∈ gray n` (`List.mem_map`).
-/
import Solutions.Circuits.Definitions

/-!
# Le code de Gray

Dans un compteur ordinaire, passer de 0111 à 1000 change 4 bits à la fois : si les bits ne
changent pas exactement au même instant, on lit n'importe quoi. Le **code de Gray** énumère tous
les mots de `n` bits de façon que deux mots consécutifs ne diffèrent que d'**un seul** bit.
(Utilisé dans les capteurs de position, les roues codeuses, les tableaux de Karnaugh…)

Construction « miroir » : on écrit la liste pour `n` bits précédée de `0`, puis la même liste
**à l'envers** précédée de `1`.

## À prouver
1. `longueur_gray : (gray n).length = 2 ^ n`
2. `mots_gray : w ∈ gray n → w.length = n`
3. `gray_quatre` : dans `gray 4`, deux mots consécutifs diffèrent d'exactement un bit.

## Ressources
- [Code de Gray (Wikipédia)](https://fr.wikipedia.org/wiki/Code_de_Gray)
-/

namespace Parcours.Circuits

def gray : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (gray n).map (false :: ·) ++ (gray n).reverse.map (true :: ·)

/-- Nombre de positions où deux mots diffèrent. -/
def ecarts (u v : List Bool) : Nat := ((List.zipWith (· != ·) u v).filter id).length

def voisins : List (List Bool) → Bool
  | u :: v :: l => ecarts u v == 1 && voisins (v :: l)
  | _ => true

theorem longueur_gray (n : Nat) : (gray n).length = 2 ^ n := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [gray, List.length_append, List.length_map, List.length_reverse, ih, Nat.pow_succ]
    omega

theorem mots_gray (n : Nat) : ∀ w ∈ gray n, w.length = n := by -- @exo
  induction n with
  | zero => simp [gray]
  | succ n ih =>
    simp only [gray, List.mem_append, List.mem_map, List.mem_reverse]
    rintro w (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) <;> simp [ih a ha]

theorem gray_quatre : voisins (gray 4) = true := by -- @exo
  decide

end Parcours.Circuits

#verifier
