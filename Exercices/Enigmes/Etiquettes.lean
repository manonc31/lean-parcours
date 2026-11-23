import Exercices.Logique.Bilan
import Exercices.Listes.Pont

/-!
# Les trois boîtes mal étiquetées

Trois boîtes sont étiquetées « Pommes », « Oranges » et « Mélange ». Toutes les étiquettes sont
**fausses**. Tu peux tirer **un seul** fruit d'**une seule** boîte, sans regarder dedans. Comment
retrouver le contenu des trois boîtes ?

Réponse : tire un fruit dans la boîte « Mélange » ! Elle ne contient pas le mélange, donc le fruit
tiré dit tout. Par exemple, si c'est une orange…

Codage : 0 = pommes, 1 = oranges, 2 = mélange. `c` donne le contenu de chaque boîte, indexée par
son étiquette.

## À prouver
`orange` : si on tire une orange de la boîte « Mélange », la seule possibilité est : la boîte
« Pommes » contient le mélange, la boîte « Oranges » les pommes, la boîte « Mélange » les oranges.

---
*Exercice* `Enigmes.Etiquettes` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Enigmes.Etiquettes` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Enigmes

def contenus : List (List Nat) :=
  [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]

def toutesFausses (c : List Nat) : Bool := (List.range 3).all fun i => c.getD i 0 != i

/-- Tirer un fruit de type `f` dans la boîte d'étiquette `b` est possible. -/
def possible (c : List Nat) (b f : Nat) : Bool := c.getD b 0 == f || c.getD b 0 == 2

theorem orange : ∀ c ∈ contenus, toutesFausses c = true → possible c 2 1 = true → c = [2, 0, 1] := by
  sorry

end Parcours.Enigmes

#verifier
