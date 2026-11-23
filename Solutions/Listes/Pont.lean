/- @parcours
titre: Le pont vers les listes de Lean
difficulte: 3
genre: pont
debloque: List
requiert: Listes.MiroirRapide, Listes.Plis, Listes.Appartenance, Listes.PrendreJeter, Listes.Filtre
indice: `versList` et `depuisList` se définissent par récurrence : `nil ↦ []`, `x ∷ l ↦ x :: versList l`.
indice: Toutes les preuves sont des récurrences où le cas `cons` se termine par `rw [ih]` (souvent après un `show` qui déplie les définitions).
indice: Pour la liste de Lean, `(x :: l₁) ++ l₂ = x :: (l₁ ++ l₂)` et `(x :: l).length = l.length + 1` sont vrais par définition.
-/
import Solutions.Listes.Map

/-!
# 🌉 Le pont vers les listes de Lean

Les listes de Lean (`List α`, écrites `[a, b, c]` avec `::` et `++`) sont exactement tes `Liste α`.
Construis les traductions dans les deux sens et prouve qu'elles respectent tout.

🔑 **Récompense** : débloque le jeton **`List`** : tous les lemmes `List.*` de la bibliothèque
(et `simp` sur les listes) deviennent purs pour la suite.

## À faire
1. `versList : Liste α → List α` et `depuisList : List α → Liste α` (à programmer)
2. `depuis_vers (l : Liste α) : depuisList (versList l) = l`
3. `vers_depuis (l : List α) : versList (depuisList l) = l`
4. `versList_concat : versList (l₁ ++ l₂) = versList l₁ ++ versList l₂`
5. `longueur_eq_length : longueur l = (versList l).length`
6. `versList_map : versList (map f l) = (versList l).map f`
-/

namespace Parcours.Listes.Liste

variable {α β : Type}

def versList : Liste α → List α -- @exo
  | nil => []
  | x ∷ l => x :: versList l

def depuisList : List α → Liste α -- @exo
  | [] => nil
  | x :: l => x ∷ depuisList l

theorem depuis_vers (l : Liste α) : depuisList (versList l) = l := by -- @exo
  induction l with
  | nil => rfl
  | cons x l ih =>
    show x ∷ depuisList (versList l) = x ∷ l
    rw [ih]

theorem vers_depuis (l : List α) : versList (depuisList l) = l := by -- @exo
  induction l with
  | nil => rfl
  | cons x l ih =>
    show x :: versList (depuisList l) = x :: l
    rw [ih]

theorem versList_concat (l₁ l₂ : Liste α) : versList (l₁ ++ l₂) = versList l₁ ++ versList l₂ := by -- @exo
  induction l₁ with
  | nil => rfl
  | cons x l ih =>
    show x :: versList (l ++ l₂) = x :: versList l ++ versList l₂
    rw [ih]
    rfl

theorem longueur_eq_length (l : Liste α) : longueur l = (versList l).length := by -- @exo
  induction l with
  | nil => rfl
  | cons x l ih =>
    show longueur l + 1 = (versList l).length + 1
    rw [ih]

theorem versList_map (f : α → β) (l : Liste α) : versList (map f l) = (versList l).map f := by -- @exo
  induction l with
  | nil => rfl
  | cons x l ih =>
    show f x :: versList (map f l) = f x :: (versList l).map f
    rw [ih]

end Parcours.Listes.Liste

#verifier
