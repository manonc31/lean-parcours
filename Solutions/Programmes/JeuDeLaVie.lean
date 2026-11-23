/- @parcours
titre: Le jeu de la vie
difficulte: 2
requiert: Programmes.Magicien
indice: Ce sont des simulations : `decide` (ou `decide +kernel`).
indice: Les coordonnées commencent à 2 pour éviter les soustractions tronquées de `Nat` au bord.
-/
import Solutions.Programmes.Definitions

/-!
# Le jeu de la vie

Le **jeu de la vie** de John Conway (1970) : sur une grille infinie, chaque cellule est vivante
ou morte. À chaque génération, une cellule morte avec exactement 3 voisines vivantes naît ; une
cellule vivante avec 2 ou 3 voisines survit ; les autres meurent. De ces règles minuscules naissent
des comportements incroyables (le jeu de la vie peut même simuler un ordinateur !).

Les cellules vivantes sont une liste de coordonnées.

## À prouver
1. `bloc_stable` : le bloc 2 × 2 ne bouge pas.
2. `clignotant_periode` : le clignotant (3 cellules en ligne) revient après 2 générations, pas 1.
3. `planeur_avance` : après 4 générations, le **planeur** s'est déplacé d'une case en diagonale.

## Ressources
- [Jeu de la vie (Wikipédia)](https://fr.wikipedia.org/wiki/Jeu_de_la_vie)
- [Simulateur en ligne (playgameoflife.com)](https://playgameoflife.com/)
-/

namespace Parcours.Prog

def voisinsVie (c : Nat × Nat) : List (Nat × Nat) :=
  [(c.1 - 1, c.2 - 1), (c.1 - 1, c.2), (c.1 - 1, c.2 + 1), (c.1, c.2 - 1), (c.1, c.2 + 1),
   (c.1 + 1, c.2 - 1), (c.1 + 1, c.2), (c.1 + 1, c.2 + 1)]

def nbVivantes (vie : List (Nat × Nat)) (c : Nat × Nat) : Nat :=
  ((voisinsVie c).filter (vie.contains ·)).length

def generation (vie : List (Nat × Nat)) : List (Nat × Nat) :=
  (vie ++ vie.flatMap voisinsVie).eraseDups.filter fun c =>
    nbVivantes vie c == 3 || (nbVivantes vie c == 2 && vie.contains c)

def memes (a b : List (Nat × Nat)) : Bool := a.all (b.contains ·) && b.all (a.contains ·)

def bloc : List (Nat × Nat) := [(2, 2), (2, 3), (3, 2), (3, 3)]
def clignotant : List (Nat × Nat) := [(3, 2), (3, 3), (3, 4)]
def planeur : List (Nat × Nat) := [(2, 3), (3, 4), (4, 2), (4, 3), (4, 4)]

theorem bloc_stable : memes (generation bloc) bloc = true := by -- @exo
  decide

theorem clignotant_periode : memes (repeter generation 2 clignotant) clignotant = true ∧
    memes (generation clignotant) clignotant = false := by -- @exo
  decide

theorem planeur_avance :
    memes (repeter generation 4 planeur) (planeur.map fun c => (c.1 + 1, c.2 + 1)) = true := by -- @exo
  decide +kernel

end Parcours.Prog

#verifier
