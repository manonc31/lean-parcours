import Exercices.Listes.Pont
import Exercices.Recurrence.Definitions

/-!
# Les symétries du triangle

Un triangle équilatéral a 6 symétries : 3 rotations (0°, 120°, 240°) et 3 réflexions. Elles
forment le groupe `S₃`, le plus petit groupe **non commutatif** : tourner puis retourner n'est pas
la même chose que retourner puis tourner !

Une symétrie est codée par la liste des images des sommets 0, 1, 2. `r` est la rotation d'un tiers
de tour, `s` la réflexion qui fixe le sommet 0.

## À prouver
1. `r_cube : r³ = id` et `s_carre : s² = id`
2. `non_commutatif : r ∘ s ≠ s ∘ r`
3. `relation : s ∘ r ∘ s = r⁻¹ = r²` (la relation des groupes diédraux)
4. `six` : en composant `r` et `s` de toutes les façons, on obtient exactement 6 symétries.

## Ressources
- [Groupe diédral (Wikipédia)](https://fr.wikipedia.org/wiki/Groupe_di%C3%A9dral)

---
*Exercice* `Algebre.Triangle` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Algebre.Triangle` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Algebre

def comp (a b : List Nat) : List Nat := b.map (a.getD · 0)

def ident : List Nat := [0, 1, 2]
def r : List Nat := [1, 2, 0]
def s : List Nat := [0, 2, 1]

theorem r_cube : comp r (comp r r) = ident := by
  sorry

theorem s_carre : comp s s = ident := by
  sorry

theorem non_commutatif : comp r s ≠ comp s r := by
  sorry

theorem relation : comp s (comp r s) = comp r r := by
  sorry

def engendres : List (List Nat) :=
  [ident, r, comp r r, s, comp r s, comp (comp r r) s]

theorem six : engendres.eraseDups.length = 6 ∧
    ∀ a ∈ engendres, ∀ b ∈ engendres, comp a b ∈ engendres := by
  sorry

end Parcours.Algebre

#verifier
