import Exercices.Graphes.Definitions

/-!
# Colorier avec deux couleurs

Un graphe est **biparti** si on peut colorier ses sommets en deux couleurs de sorte que chaque
arête relie deux couleurs différentes (exemple : des employés et des tâches). Un carré est biparti ;
un triangle ne l'est pas.

## À prouver
1. `carre_biparti : ∃ c, Coloriage [(0,1), (1,2), (2,3), (3,0)] c`
2. `triangle_pas_biparti : ¬∃ c, Coloriage [(0,1), (1,2), (2,0)] c`

## Ressources
- [Graphe biparti (Wikipédia)](https://fr.wikipedia.org/wiki/Graphe_biparti)

---
*Exercice* `Graphes.Coloriage` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Graphes.Coloriage` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Graphes

def Coloriage (g : Graphe) (c : Nat → Bool) : Prop := ∀ e ∈ g, c e.1 ≠ c e.2

instance (g : Graphe) (c : Nat → Bool) : Decidable (Coloriage g c) := by
  unfold Coloriage; infer_instance

theorem carre_biparti : ∃ c, Coloriage [(0, 1), (1, 2), (2, 3), (3, 0)] c := by
  sorry

theorem triangle_pas_biparti : ¬∃ c, Coloriage [(0, 1), (1, 2), (2, 0)] c := by
  sorry

end Parcours.Graphes

#verifier
