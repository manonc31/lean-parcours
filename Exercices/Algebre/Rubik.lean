import Exercices.Listes.Pont
import Exercices.Recurrence.Definitions

/-!
# Le Rubik's cube

Les mouvements du Rubik's cube forment un **groupe** : on peut les composer, et chacun a un
inverse. Un fait étonnant : si on répète la séquence « R puis U » (tourner la face droite, puis
la face du haut, d'un quart de tour), le cube revient à son état de départ après exactement
**105** répétitions. Et le célèbre « sexy move » `R U R⁻¹ U⁻¹` revient au départ après 6.

Le cube est codé par ses 54 facettes, numérotées de 0 à 53 ; un mouvement est la liste qui dit,
pour chaque case, de quelle case vient la facette qui s'y trouve après le mouvement.

## À prouver
1. `quatre_quarts : R⁴ = identité`
2. `cent_cinq : (RU)¹⁰⁵ = identité`
3. `pas_moins` : `(RU)¹⁵`, `(RU)²¹` et `(RU)³⁵` ne sont pas l'identité. Comme l'ordre de `RU`
   divise 105 = 3 × 5 × 7 (théorème de Lagrange), c'est donc exactement 105.
4. `sexy_move : (R U R⁻¹ U⁻¹)⁶ = identité`

## Ressources
- [Groupe du Rubik's Cube (Wikipédia)](https://fr.wikipedia.org/wiki/Groupe_du_Rubik%27s_Cube)

---
*Exercice* `Algebre.Rubik` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Algebre.Rubik` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Algebre

def appliquer (mvt etat : List Nat) : List Nat := mvt.map (etat.getD · 0)

def mouvementR : List Nat :=
  [0, 1, 2, 3, 4, 5, 26, 25, 24, 15, 12, 9, 16, 13, 10, 17, 14, 11,
   18, 19, 20, 21, 22, 23, 33, 34, 35, 27, 28, 29, 30, 31, 32, 53, 52, 51,
   36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 6, 7, 8]

def mouvementU : List Nat :=
  [2, 5, 8, 1, 4, 7, 0, 3, 6, 9, 10, 11, 12, 13, 14, 47, 50, 53,
   18, 19, 17, 21, 22, 16, 24, 25, 15, 27, 28, 29, 30, 31, 32, 33, 34, 35,
   36, 37, 38, 39, 40, 41, 20, 23, 26, 45, 46, 44, 48, 49, 43, 51, 52, 42]

def depart : List Nat := List.range 54

/-- `puissance f n x` applique `n` fois `f`. -/
def puissance (f : List Nat → List Nat) : Nat → List Nat → List Nat
  | 0, x => x
  | n + 1, x => puissance f n (f x)

def RU (e : List Nat) : List Nat := appliquer mouvementU (appliquer mouvementR e)

def sexy (e : List Nat) : List Nat :=
  puissance (appliquer mouvementU) 3 (puissance (appliquer mouvementR) 3 (RU e))

theorem quatre_quarts : puissance (appliquer mouvementR) 4 depart = depart := by
  sorry

theorem cent_cinq : puissance RU 105 depart = depart := by
  sorry

theorem pas_moins : puissance RU 15 depart ≠ depart ∧ puissance RU 21 depart ≠ depart ∧
    puissance RU 35 depart ≠ depart := by
  sorry

theorem sexy_move : puissance sexy 6 depart = depart := by
  sorry

end Parcours.Algebre

#verifier
