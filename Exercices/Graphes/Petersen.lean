import Exercices.Graphes.Definitions

/-!
# Le graphe de Petersen

Le graphe de Petersen (1898) est le contre-exemple préféré des théoriciens des graphes : 10
sommets, 15 arêtes, chaque sommet a 3 voisins, il n'a ni triangle ni carré… Un pentagone extérieur
(0–4), une étoile intérieure (5–9), et des rayons.

## À prouver
1. `quinze_aretes`, `trois_voisins`
2. `sans_triangle` : aucun triangle.
3. `trois_couleurs` : on peut le colorier avec 3 couleurs, mais `pas_deux` : pas avec 2 (il contient
   un cycle de longueur 5).

## Ressources
- [Graphe de Petersen (Wikipédia)](https://fr.wikipedia.org/wiki/Graphe_de_Petersen)

---
*Exercice* `Graphes.Petersen` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Graphes.Petersen` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Graphes

def petersen : Graphe :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5),
   (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)]

def adjacents (g : Graphe) (u v : Nat) : Bool := g.contains (u, v) || g.contains (v, u)

theorem quinze_aretes : petersen.length = 15 := by
  sorry

theorem trois_voisins : (List.range 10).all (fun v => degre petersen v == 3) = true := by
  sorry

theorem sans_triangle : ∀ a, a < 10 → ∀ b, b < 10 → ∀ c, c < 10 →
    !(adjacents petersen a b && adjacents petersen b c && adjacents petersen a c) = true := by
  sorry

def couleurs3 : List Nat := [0, 1, 0, 1, 2, 1, 2, 2, 0, 0]

theorem trois_couleurs : petersen.all (fun e => couleurs3.getD e.1 0 != couleurs3.getD e.2 0) = true := by
  sorry

def colorations2 : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (colorations2 n).flatMap fun c => [false :: c, true :: c]

theorem pas_deux : ∀ c ∈ colorations2 10, petersen.any (fun e => c.getD e.1 false == c.getD e.2 false) = true := by
  sorry

end Parcours.Graphes

#verifier
