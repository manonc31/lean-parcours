import ParcoursOutils

/-!
# Réécrire à l'envers

Ici `h : 4 = y` : on veut remplacer `y` par `4`, c'est-à-dire réécrire de **droite à gauche** : `rw [← h]` (la flèche se tape `\l`).

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.RwArriere` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Gymnase.RwArriere` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem rw_arriere (y : Nat) (h : 4 = y) : y + 1 = 5 := by
  sorry

end Parcours.Gymnase

#verifier
