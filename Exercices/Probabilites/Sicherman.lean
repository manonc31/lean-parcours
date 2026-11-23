import Exercices.Probabilites.Definitions

/-!
# Les dés de Sicherman

Deux dés bizarres : l'un porte `1, 2, 2, 3, 3, 4`, l'autre `1, 3, 4, 5, 6, 8`. Surprise : la
somme de ces deux dés a **exactement** la même loi que la somme de deux dés ordinaires ! (George
Sicherman, 1978 ; c'est la seule autre paire possible avec des faces positives.)

## À prouver
`sicherman` : pour chaque total de 2 à 12, il y a autant de façons de l'obtenir.

## Ressources
- [Dés de Sicherman (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Sicherman_dice)

---
*Exercice* `Probabilites.Sicherman` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Probabilites.Sicherman` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Proba

def deS1 : List Nat := [1, 2, 2, 3, 3, 4]
def deS2 : List Nat := [1, 3, 4, 5, 6, 8]

def sommes (x y : List Nat) : List Nat := x.flatMap fun a => y.map fun b => a + b

theorem sicherman : ∀ s, s < 13 → (sommes deS1 deS2).count s = (sommes de de).count s := by
  sorry

end Parcours.Proba

#verifier
