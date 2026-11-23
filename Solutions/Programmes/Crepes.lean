/- @parcours
titre: Le tri des crêpes
difficulte: 2
requiert: Programmes.Carrousel
indice: Sépare les cas `k ≤ l.length` ou non.
indice: Lemmes utiles : `List.take_append_of_le_length`, `List.drop_append_of_le_length`, `List.take_of_length_le`, `List.drop_of_length_le`.
-/
import Solutions.Programmes.Definitions

/-!
# Le tri des crêpes

Un cuisinier a une pile de crêpes de tailles différentes. Il ne sait faire qu'une chose : glisser
sa spatule sous la `k`-ième crêpe et **retourner** tout le haut de la pile. Peut-il trier la pile ?
Oui : amener la plus grande en haut, puis la retourner tout en bas, et recommencer.
(Bill Gates a publié un article de recherche sur ce problème quand il était étudiant !)

## À prouver
1. `retourner_retourner : retourner k (retourner k l) = l`
2. `longueur_retourner : (retourner k l).length = l.length`
3. `trier_trois : retourner 2 (retourner 3 [3, 1, 2]) = [1, 2, 3]`

## Ressources
- [Tri de crêpes (Wikipédia)](https://fr.wikipedia.org/wiki/Tri_de_cr%C3%AApes)
-/

namespace Parcours.Prog

def retourner {α : Type} (k : Nat) (l : List α) : List α := (l.take k).reverse ++ l.drop k

theorem longueur_retourner {α : Type} (k : Nat) (l : List α) :
    (retourner k l).length = l.length := by -- @exo
  simp only [retourner, List.length_append, List.length_reverse, List.length_take, List.length_drop]
  omega

theorem retourner_retourner {α : Type} (k : Nat) (l : List α) :
    retourner k (retourner k l) = l := by -- @exo
  unfold retourner
  by_cases h : k ≤ l.length
  · have hl : ((l.take k).reverse).length = k := by simp; omega
    rw [List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega),
      List.take_of_length_le (by omega), List.drop_of_length_le (by omega)]
    simp
  · have h1 : l.take k = l := List.take_of_length_le (by omega)
    have h2 : l.drop k = [] := List.drop_of_length_le (by omega)
    rw [h1, h2, List.append_nil, List.take_of_length_le (by simp; omega),
      List.drop_of_length_le (by simp; omega)]
    simp

theorem trier_trois : retourner 2 (retourner 3 [3, 1, 2]) = [1, 2, 3] := by -- @exo
  decide

end Parcours.Prog

#verifier
