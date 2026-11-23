/- @parcours
titre: Colorier avec deux couleurs
difficulte: 2
indice: `carre_biparti` : propose `fun v => v % 2 == 0` et laisse `decide` vérifier les 4 arêtes.
indice: `triangle_pas_biparti` : suppose un coloriage `c`. Applique-le aux trois arêtes (`hc (0, 1) (by simp)`…) : trois couleurs deux à deux différentes avec seulement deux couleurs, impossible. `revert` les trois hypothèses, puis `cases c 0 <;> cases c 1 <;> cases c 2 <;> decide`.
-/
import Solutions.Graphes.Definitions

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
-/

namespace Parcours.Graphes

def Coloriage (g : Graphe) (c : Nat → Bool) : Prop := ∀ e ∈ g, c e.1 ≠ c e.2

instance (g : Graphe) (c : Nat → Bool) : Decidable (Coloriage g c) := by
  unfold Coloriage; infer_instance

theorem carre_biparti : ∃ c, Coloriage [(0, 1), (1, 2), (2, 3), (3, 0)] c := by -- @exo
  exact ⟨fun v => v % 2 == 0, by decide⟩

theorem triangle_pas_biparti : ¬∃ c, Coloriage [(0, 1), (1, 2), (2, 0)] c := by -- @exo
  rintro ⟨c, hc⟩
  have h1 := hc (0, 1) (by simp)
  have h2 := hc (1, 2) (by simp)
  have h3 := hc (2, 0) (by simp)
  revert h1 h2 h3
  cases c 0 <;> cases c 1 <;> cases c 2 <;> decide

end Parcours.Graphes

#verifier
