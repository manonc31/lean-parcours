/- @parcours
titre: Le pont et la lampe
difficulte: 2
requiert: Enigmes.Missionnaires
indice: L'astuce : faire traverser **ensemble** les deux plus lents (5 et 10).
indice: Pour que ce soit possible, il faut qu'un rapide soit déjà de l'autre côté pour ramener la lampe.
-/
import Solutions.Listes.Pont
import Solutions.Recurrence.Definitions

/-!
# Le pont et la lampe

Quatre personnes doivent traverser un pont de nuit, avec une seule lampe. Le pont supporte au
plus deux personnes, et il faut la lampe pour traverser. Elles mettent 1, 2, 5 et 10 minutes ;
à deux, on va au rythme du plus lent. La lampe doit être rapportée à chaque fois.
Peut-on traverser en 17 minutes ? (Indice : ce n'est pas en faisant tout raccompagner par le plus
rapide, qui donne 19 minutes.)

Chaque personne est désignée par son temps. Une stratégie est la liste des groupes qui traversent,
alternativement à l'aller et au retour.

## À faire
1. Écris `solutionPont` et prouve `dix_sept : traverser [1, 2, 5, 10] [] true solutionPont = some 17`.
2. `optimal` : la recherche exhaustive parmi toutes les stratégies en 5 traversées (le minimum
   pour 4 personnes) ne fait pas mieux que 17.

## Ressources
- [Le problème du pont et de la torche (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Bridge_and_torch_problem)
-/

namespace Parcours.Enigmes

/-- `traverser gauche droite aller groupes` : le temps total, ou `none` si la stratégie est invalide. -/
def traverser : List Nat → List Nat → Bool → List (List Nat) → Option Nat
  | g, _, _, [] => if g.isEmpty then some 0 else none
  | g, d, aller, grp :: r =>
    if (grp.length == 1 || grp.length == 2) && grp.eraseDups == grp &&
        grp.all ((if aller then g else d).contains ·) then
      (if aller then traverser (g.removeAll grp) (d ++ grp) false r
       else traverser (g ++ grp) (d.removeAll grp) true r).map (grp.foldl max 0 + ·)
    else none

def solutionPont : List (List Nat) := -- @exo
  [[1, 2], [1], [5, 10], [2], [1, 2]]

theorem dix_sept : traverser [1, 2, 5, 10] [] true solutionPont = some 17 := by -- @exo
  decide

/-- Pour la recherche exhaustive, on code un groupe de personnes par un nombre binaire (un
« masque ») : le bit 0 pour la personne de 1 min, le bit 1 pour 2 min, le bit 2 pour 5 min,
le bit 3 pour 10 min. `tempsGroupe` donne le temps de traversée d'un groupe. -/
def tempsGroupe : Nat → Nat
  | 1 => 1 | 2 => 2 | 4 => 5 | 8 => 10
  | 3 => 2 | 5 => 5 | 6 => 5 | 9 => 10 | 10 => 10 | 12 => 10
  | _ => 0

def groupesMasques : List Nat := [1, 2, 4, 8, 3, 5, 6, 9, 10, 12]

/-- Le meilleur temps en au plus `f` traversées, si le masque `g` est sur la rive de départ. -/
def meilleur : Nat → Nat → Bool → Option Nat
  | _, 0, _ => some 0
  | 0, _, _ => none
  | f + 1, g, aller =>
    (groupesMasques.filterMap fun grp =>
      if grp &&& (if aller then g else 15 - g) == grp then
        (meilleur f (if aller then g - grp else g + grp) (!aller)).map (tempsGroupe grp + ·)
      else none).min?

theorem optimal : meilleur 5 15 true = some 17 := by -- @exo
  decide +kernel

end Parcours.Enigmes

#verifier
