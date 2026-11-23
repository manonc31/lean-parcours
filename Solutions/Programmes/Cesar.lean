/- @parcours
titre: Le chiffre de César
difficulte: 2
requiert: Programmes.Accumulateur
indice: `List.map_map` fusionne deux `map`, et `List.map_congr_left` permet de comparer deux `map` élément par élément.
indice: Sur chaque élément, il reste une égalité avec des `% 26` : `omega`.
indice: Pour `cesar_dechiffre`, écris `m` comme `List.map id m` (`← List.map_id`).
-/
import Solutions.Programmes.Definitions

/-!
# Le chiffre de César

Jules César chiffrait ses messages en décalant chaque lettre de 3 dans l'alphabet : A → D,
B → E, …, Z → C. Les lettres sont ici des nombres de 0 à 25, et le décalage se fait modulo 26.
« HELLO » = `[7, 4, 11, 11, 14]` devient « KHOOR ».

## À prouver
1. `cesar_compose : cesar a (cesar b m) = cesar (a + b) m` (deux décalages font un décalage)
2. `cesar_dechiffre` : décaler de `26 - k` annule un décalage de `k` (pour un vrai message)
3. `rot13` : ROT13 (décalage de 13, utilisé sur les forums pour cacher les spoilers !) est son
   propre inverse.
4. `hello : cesar 3 [7, 4, 11, 11, 14] = [10, 7, 14, 14, 17]`

## Ressources
- [Chiffrement par décalage (Wikipédia)](https://fr.wikipedia.org/wiki/Chiffrement_par_d%C3%A9calage)
-/

namespace Parcours.Prog

def decaler (k x : Nat) : Nat := (x + k) % 26

def cesar (k : Nat) (m : List Nat) : List Nat := m.map (decaler k)

theorem cesar_compose (a b : Nat) (m : List Nat) : cesar a (cesar b m) = cesar (a + b) m := by -- @exo
  simp only [cesar, List.map_map]
  apply List.map_congr_left
  intro x _
  simp only [Function.comp_apply, decaler]
  omega

theorem cesar_dechiffre (k : Nat) (m : List Nat) (h : ∀ x ∈ m, x < 26) :
    cesar (26 - k % 26) (cesar k m) = m := by -- @exo
  rw [cesar_compose]
  conv => rhs; rw [← List.map_id m]
  apply List.map_congr_left
  intro x hx
  have := h x hx
  simp only [decaler, id]
  omega

theorem rot13 (m : List Nat) (h : ∀ x ∈ m, x < 26) : cesar 13 (cesar 13 m) = m := by -- @exo
  simpa using cesar_dechiffre 13 m h

theorem hello : cesar 3 [7, 4, 11, 11, 14] = [10, 7, 14, 14, 17] := by -- @exo
  decide

end Parcours.Prog

#verifier
