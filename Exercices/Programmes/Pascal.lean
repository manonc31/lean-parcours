import Exercices.Programmes.Definitions

/-!
# Le triangle de Pascal en listes

Chaque ligne du triangle de Pascal s'obtient en additionnant la ligne précédente décalée et
la ligne précédente : `[1, 3, 3, 1]` → `[0, 1, 3, 3, 1] + [1, 3, 3, 1, 0] = [1, 4, 6, 4, 1]`.
Conséquence : la somme double à chaque ligne, donc la ligne `n` a pour somme `2^n`.

## À prouver
1. `somme_zipWith` : la somme de deux listes additionnées terme à terme.
2. `longueur_pascal : (pascal n).length = n + 1`
3. `somme_pascal : (pascal n).sum = 2 ^ n`
4. `ligne_quatre : pascal 4 = [1, 4, 6, 4, 1]`

## Ressources
- [Triangle de Pascal (Wikipédia)](https://fr.wikipedia.org/wiki/Triangle_de_Pascal)

---
*Exercice* `Programmes.Pascal` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Programmes.Pascal` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

def ligneSuivante (l : List Nat) : List Nat := List.zipWith (· + ·) (0 :: l) (l ++ [0])

def pascal : Nat → List Nat
  | 0 => [1]
  | n + 1 => ligneSuivante (pascal n)

theorem somme_zipWith (a b : List Nat) (h : a.length = b.length) :
    (List.zipWith (· + ·) a b).sum = a.sum + b.sum := by
  sorry

theorem longueur_pascal (n : Nat) : (pascal n).length = n + 1 := by
  sorry

theorem somme_pascal (n : Nat) : (pascal n).sum = 2 ^ n := by
  sorry

theorem ligne_quatre : pascal 4 = [1, 4, 6, 4, 1] := by
  sorry

end Parcours.Prog

#verifier
