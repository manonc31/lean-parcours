/- @parcours
titre: La compression RLE
difficulte: 3
indice: Récurrence sur `l`. Dans le cas `x :: l`, déplie `encoder` et analyse `encoder l` : `simp only [encoder]`, puis `split` (pour le `match`) et encore `split` (pour le `if`).
indice: Garde l'hypothèse de récurrence sous la forme `decoder (encoder l) = l`, et réécris `encoder l` grâce à l'équation donnée par `split` (`rename_i` pour nommer les variables).
indice: `decoder ((y, k + 1) :: r) = y :: decoder ((y, k) :: r)` : `simp [decoder, List.replicate_succ]`.
-/
import Solutions.Algorithmes.Definitions

/-!
# La compression RLE

« Run-length encoding » : `[5, 5, 5, 2, 2, 7]` devient `[(5, 3), (2, 2), (7, 1)]`
(la valeur, puis combien de fois elle se répète). C'est l'une des plus vieilles méthodes de
compression (fax, images BMP, PCX…). Un compresseur doit être **sans perte** : décompresser
redonne exactement l'original. Prouve-le !

## À prouver
`decoder_encoder (l : List Nat) : decoder (encoder l) = l`

## Ressources
- [Run-length encoding (Wikipédia)](https://fr.wikipedia.org/wiki/Run-length_encoding)
-/

namespace Parcours.Algo

def encoder : List Nat → List (Nat × Nat)
  | [] => []
  | x :: l =>
    match encoder l with
    | (y, k) :: r => if x = y then (y, k + 1) :: r else (x, 1) :: (y, k) :: r
    | [] => [(x, 1)]

def decoder (l : List (Nat × Nat)) : List Nat := l.flatMap (fun p => List.replicate p.2 p.1)

example : encoder [5, 5, 5, 2, 2, 7] = [(5, 3), (2, 2), (7, 1)] := by decide

theorem decoder_encoder (l : List Nat) : decoder (encoder l) = l := by -- @exo
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [encoder]
    split
    · rename_i y k r heq
      rw [heq] at ih
      split
      · rename_i hxy
        subst hxy
        simp only [decoder, List.flatMap_cons, List.replicate_succ] at ih ⊢
        rw [List.cons_append, ih]
      · simp only [decoder, List.flatMap_cons] at ih ⊢
        rw [ih]
        rfl
    · rename_i heq
      rw [heq] at ih
      simp only [decoder, List.flatMap_cons, List.flatMap_nil] at ih ⊢
      rw [← ih]
      rfl

end Parcours.Algo

#verifier
