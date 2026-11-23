import Exercices.Programmes.Definitions

/-!
# Le sac à dos

Un cambrioleur a un sac qui supporte 10 kg. Quels objets emporter pour maximiser la valeur ?
La **programmation dynamique** (Bellman, années 1950) répond avec une équation : pour le premier
objet, soit on le laisse, soit on le prend (s'il rentre), et on garde le meilleur des deux.

On prouve que cette équation donne vraiment l'optimum : elle majore la valeur de **tout** choix
d'objets possible, et elle est atteinte.

## À prouver
1. `sac_majore` : aucun choix qui rentre dans le sac ne vaut plus que `sac l c`.
2. `sac_atteint` : il existe un choix qui atteint `sac l c`.
3. `cambriolage : sac objets 10 = 113`

## Ressources
- [Problème du sac à dos (Wikipédia)](https://fr.wikipedia.org/wiki/Probl%C3%A8me_du_sac_%C3%A0_dos)

---
*Exercice* `Programmes.SacADos` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Programmes.SacADos` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

/-- Les objets sont des couples (poids, valeur). -/
def sac : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | (w, v) :: r, c => if w ≤ c then max (sac r c) (v + sac r (c - w)) else sac r c

def parties {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: l => parties l ++ (parties l).map (x :: ·)

def poidsSac (s : List (Nat × Nat)) : Nat := (s.map Prod.fst).sum
def valeurSac (s : List (Nat × Nat)) : Nat := (s.map Prod.snd).sum

theorem sac_majore (l : List (Nat × Nat)) (c : Nat) :
    ∀ s ∈ parties l, poidsSac s ≤ c → valeurSac s ≤ sac l c := by
  sorry

theorem sac_atteint (l : List (Nat × Nat)) (c : Nat) :
    ∃ s ∈ parties l, poidsSac s ≤ c ∧ valeurSac s = sac l c := by
  sorry

def objets : List (Nat × Nat) := [(5, 10), (4, 40), (6, 30), (3, 50), (2, 15), (1, 8)]

theorem cambriolage : sac objets 10 = 113 := by
  sorry

end Parcours.Prog

#verifier
