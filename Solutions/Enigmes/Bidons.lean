/- @parcours
titre: Les bidons de Die Hard
difficulte: 2
requiert: Enigmes.LoupChevreChou
indice: Remplis le grand bidon, et verse-le dans le petit : il reste 2 litres dans le grand.
indice: Vide le petit, mets-y les 2 litres, remplis le grand, et complète le petit…
-/
import Solutions.Listes.Pont
import Solutions.Recurrence.Definitions

/-!
# Les bidons de Die Hard

Dans le film *Die Hard 3*, les héros doivent désamorcer une bombe en posant exactement 4 litres
d'eau sur une balance. Ils n'ont qu'un bidon de 3 litres, un bidon de 5 litres, et une fontaine.
On peut remplir un bidon, le vider, ou verser l'un dans l'autre (jusqu'à ce que l'un soit vide ou
l'autre plein).

## À faire
Écris `solutionBidons` (la liste des états successifs `(bidon de 3 L, bidon de 5 L)`, en partant
de `(0, 0)`) et vérifie-la avec `decide`.

## Ressources
- [Problème des bidons (Wikipédia)](https://fr.wikipedia.org/wiki/Probl%C3%A8me_des_bidons)
-/

namespace Parcours.Enigmes

/-- (contenu du petit bidon, contenu du grand). -/
abbrev Contenu := Nat × Nat

/-- Les états atteignables en un coup, avec des bidons de capacités `A` et `B`. -/
def suivants (A B : Nat) (e : Contenu) : List Contenu :=
  [(A, e.2), (e.1, B), (0, e.2), (e.1, 0),
   (e.1 - min e.1 (B - e.2), e.2 + min e.1 (B - e.2)),
   (e.1 + min e.2 (A - e.1), e.2 - min e.2 (A - e.1))]

def cheminBidons (A B : Nat) : List Contenu → Bool
  | e :: e' :: r => (suivants A B e).contains e' && cheminBidons A B (e' :: r)
  | _ => true

def Obtient (A B but : Nat) (s : List Contenu) : Bool :=
  s.head? == some (0, 0) && cheminBidons A B s &&
    s.getLast?.any (fun e => e.1 == but || e.2 == but)

def solutionBidons : List Contenu := -- @exo
  [(0, 0), (0, 5), (3, 2), (0, 2), (2, 0), (2, 5), (3, 4)]

theorem die_hard : Obtient 3 5 4 solutionBidons = true := by -- @exo
  decide

end Parcours.Enigmes

#verifier
