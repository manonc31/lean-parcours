import Exercices.Programmes.Definitions

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

---
*Exercice* `Programmes.Crepes` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Programmes.Crepes` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

def retourner {α : Type} (k : Nat) (l : List α) : List α := (l.take k).reverse ++ l.drop k

theorem longueur_retourner {α : Type} (k : Nat) (l : List α) :
    (retourner k l).length = l.length := by
  sorry

theorem retourner_retourner {α : Type} (k : Nat) (l : List α) :
    retourner k (retourner k l) = l := by
  sorry

theorem trier_trois : retourner 2 (retourner 3 [3, 1, 2]) = [1, 2, 3] := by
  sorry

end Parcours.Prog

#verifier
