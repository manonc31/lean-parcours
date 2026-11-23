import Exercices.Programmes.Definitions

/-!
# Rendre la monnaie

L'algorithme **glouton** du caissier : rendre d'abord le plus possible de la plus grosse pièce,
puis de la suivante, etc. Avec les euros, il rend toujours le minimum de pièces. Mais avec des
pièces de 4, 3 et 1, il se trompe : pour rendre 6, il donne 4 + 1 + 1 au lieu de 3 + 3 !

## À prouver
1. `rendu_somme` : si la dernière pièce vaut 1, le glouton rend exactement la bonne somme.
2. `euros` : pour rendre 3,88 €, le glouton donne une pièce de chaque.
3. `glouton_rate` : avec les pièces 4, 3, 1, le glouton n'est pas optimal.

## Ressources
- [Problème du rendu de monnaie (Wikipédia)](https://fr.wikipedia.org/wiki/Probl%C3%A8me_du_rendu_de_monnaie)

---
*Exercice* `Programmes.Monnaie` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Programmes.Monnaie` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

def rendu : List Nat → Nat → List Nat
  | [], _ => []
  | p :: ps, n => List.replicate (n / p) p ++ rendu ps (n % p)

theorem rendu_somme (ps : List Nat) (n : Nat) : (rendu (ps ++ [1]) n).sum = n := by
  sorry

theorem euros : rendu [200, 100, 50, 20, 10, 5, 2, 1] 388 = [200, 100, 50, 20, 10, 5, 2, 1] := by
  sorry

theorem glouton_rate : (rendu [4, 3, 1] 6).length = 3 ∧ [3, 3].sum = 6 ∧ [3, 3].length = 2 := by
  sorry

end Parcours.Prog

#verifier
