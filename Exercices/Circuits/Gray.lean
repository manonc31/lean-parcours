import Exercices.Circuits.Definitions

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

---
*Exercice* `Circuits.Gray` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Circuits.Gray` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
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

theorem longueur_gray (n : Nat) : (gray n).length = 2 ^ n := by
  sorry

theorem mots_gray (n : Nat) : ∀ w ∈ gray n, w.length = n := by
  sorry

theorem gray_quatre : voisins (gray 4) = true := by
  sorry

end Parcours.Circuits

#verifier
