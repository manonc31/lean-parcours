/- @parcours
titre: Le problème de Monty Hall
difficulte: 2
indice: Lis bien le modèle : `presentateur v c` est la porte ouverte par le présentateur quand la voiture est derrière `v` et que le candidat a choisi `c`.
indice: Puis `decide`. Et convaincs-toi que le résultat est juste : en changeant, on gagne exactement quand le premier choix était **mauvais**, ce qui arrive 2 fois sur 3.
-/
import Solutions.Probabilites.Definitions

/-!
# Le problème de Monty Hall

Un jeu télévisé : trois portes, une voiture derrière l'une, des chèvres derrière les autres.
Tu choisis une porte. Le présentateur, qui sait où est la voiture, ouvre une **autre** porte
cachant une chèvre, et te propose de **changer**. Faut-il changer ?

Réponse (qui a fait enrager des milliers de mathématiciens en 1990) : **oui**, on gagne avec
probabilité 2/3 en changeant, contre 1/3 en gardant sa porte.

Modèle : la voiture `v` et le choix `c` sont uniformes parmi `{0, 1, 2}` (9 issues).

## À prouver
1. `garder : ProbaEst issues gagneEnGardant 1 3`
2. `changer : ProbaEst issues gagneEnChangeant 2 3`

## Ressources
- [Problème de Monty Hall (Wikipédia)](https://fr.wikipedia.org/wiki/Probl%C3%A8me_de_Monty_Hall)
-/

namespace Parcours.Proba

def portes : List Nat := [0, 1, 2]

/-- (voiture, choix du candidat) : 9 issues équiprobables. -/
def issues : List (Nat × Nat) := portes.flatMap (fun v => portes.map (fun c => (v, c)))

/-- La porte ouverte par le présentateur : ni la voiture, ni le choix (la plus petite possible). -/
def presentateur (v c : Nat) : Nat :=
  if 0 ≠ v ∧ 0 ≠ c then 0 else if 1 ≠ v ∧ 1 ≠ c then 1 else 2

/-- La porte restante (ni le choix, ni celle ouverte). -/
def autre (c o : Nat) : Nat := 3 - c - o

def gagneEnGardant (i : Nat × Nat) : Bool := i.2 == i.1
def gagneEnChangeant (i : Nat × Nat) : Bool := autre i.2 (presentateur i.1 i.2) == i.1

theorem garder : ProbaEst issues gagneEnGardant 1 3 := by -- @exo
  decide

theorem changer : ProbaEst issues gagneEnChangeant 2 3 := by -- @exo
  decide

end Parcours.Proba

#verifier
