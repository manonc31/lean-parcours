/- @parcours
titre: Qui a le poisson ?
difficulte: 2
requiert: Logique.Bilan
indice: Indices 2 et 5 : quelle couleur reste pour Alice ? Puis l'indice 8…
indice: `unique` : `decide +kernel` vérifie les 24 × 24 combinaisons.
-/
import Solutions.Listes.Pont
import Solutions.Recurrence.Definitions

/-!
# Qui a le poisson ?

Une version miniature de la célèbre « énigme d'Einstein ». Alice, Bob, Chloé et David habitent
quatre maisons alignées (dans cet ordre). Chacun a un animal (chat, chien, poisson, lapin) et une
maison d'une couleur (rouge, verte, bleue, jaune), tous différents.

1. Alice n'a pas le chat.
2. Bob habite la maison rouge.
3. Le chien habite la maison bleue.
4. Chloé n'a ni le poisson ni le chat.
5. La maison d'Alice n'est pas verte.
6. Le chat est le voisin du lapin.
7. La maison de David n'est pas jaune.
8. Le poisson vit dans la maison jaune.

Qui a le poisson ? Codage : personnes 0 (Alice) à 3 (David) ; animaux 0 chat, 1 chien,
2 poisson, 3 lapin ; couleurs 0 rouge, 1 verte, 2 bleue, 3 jaune. `animal[i]` est l'animal de la
personne `i`, `couleur[i]` sa couleur.

## À faire
1. Écris `reponse` (les deux listes) et prouve `reponse_ok`.
2. `unique` : c'est la seule solution (`decide` essaie les 576 possibilités).

## Ressources
- [Énigme d'Einstein (Wikipédia)](https://fr.wikipedia.org/wiki/%C3%89nigme_d%27Einstein)
-/

namespace Parcours.Enigmes

def Indices (animal couleur : List Nat) : Bool :=
  let a := animal.getD
  let c := couleur.getD
  a 0 0 != 0 && c 1 0 == 0 &&
  (List.range 4).all (fun i => a i 0 != 1 || c i 0 == 2) &&
  a 2 0 != 2 && a 2 0 != 0 && c 0 0 != 1 &&
  (List.range 4).all (fun i => a i 0 != 0 ||
    (List.range 4).any (fun j => a j 0 == 3 && (i + 1 == j || j + 1 == i))) &&
  c 3 0 != 3 &&
  (List.range 4).all (fun i => a i 0 != 2 || c i 0 == 3)

def permutations4 : List (List Nat) :=
  [0, 1, 2, 3].flatMap fun a => [0, 1, 2, 3].flatMap fun b => [0, 1, 2, 3].flatMap fun c =>
    [0, 1, 2, 3].filterMap fun d => if [a, b, c, d].eraseDups.length == 4 then some [a, b, c, d] else none

def reponse : List Nat × List Nat := -- @exo
  ([2, 0, 3, 1], [3, 0, 1, 2])

theorem reponse_ok : Indices reponse.1 reponse.2 = true := by -- @exo
  decide

theorem unique : ∀ a ∈ permutations4, ∀ c ∈ permutations4, Indices a c = true → (a, c) = reponse := by -- @exo
  decide +kernel

end Parcours.Enigmes

#verifier
