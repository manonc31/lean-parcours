import Exercices.Listes.Pont
import Exercices.Recurrence.Definitions

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

---
*Exercice* `Enigmes.Bidons` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Enigmes.Bidons` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
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

def solutionBidons : List Contenu :=
  sorry

theorem die_hard : Obtient 3 5 4 solutionBidons = true := by
  sorry

end Parcours.Enigmes

#verifier
