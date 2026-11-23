import Exercices.Recurrence.Definitions

/-!
# Le théorème de Zermelo

Dans un jeu à deux joueurs, **fini**, **sans hasard** et **sans match nul** (échecs sans nulle,
morpion modifié, Nim…), l'un des deux joueurs a une **stratégie gagnante**. On ne sait pas
forcément lequel… mais l'un des deux peut gagner à coup sûr (Zermelo, 1913).

On modélise un jeu par un arbre : une feuille dit qui gagne ; à un nœud, le joueur au trait
choisit d'aller à gauche ou à droite. `GagneA j t` : A peut forcer la victoire dans `j`, sachant
que `t = true` signifie que c'est à A de jouer.

## À prouver
1. `zermelo : GagneA j t ∨ GagneB j t`
2. `pas_les_deux : ¬(GagneA j t ∧ GagneB j t)`

## Ressources
- [Théorème de Zermelo (Wikipédia)](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_de_Zermelo_%28th%C3%A9orie_des_jeux%29)

---
*Exercice* `Jeux.Zermelo` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Jeux.Zermelo` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Jeux

inductive Jeu where
  | fin (gagnantA : Bool)
  | coup (gauche droite : Jeu)

open Jeu

/-- A peut forcer la victoire (`t = true` : A a le trait). -/
inductive GagneA : Jeu → Bool → Prop
  | fin {t : Bool} : GagneA (fin true) t
  | coup_g {g d : Jeu} : GagneA g false → GagneA (coup g d) true
  | coup_d {g d : Jeu} : GagneA d false → GagneA (coup g d) true
  | coup_B {g d : Jeu} : GagneA g true → GagneA d true → GagneA (coup g d) false

/-- B peut forcer la victoire. -/
inductive GagneB : Jeu → Bool → Prop
  | fin {t : Bool} : GagneB (fin false) t
  | coup_g {g d : Jeu} : GagneB g true → GagneB (coup g d) false
  | coup_d {g d : Jeu} : GagneB d true → GagneB (coup g d) false
  | coup_A {g d : Jeu} : GagneB g false → GagneB d false → GagneB (coup g d) true

theorem zermelo (j : Jeu) (t : Bool) : GagneA j t ∨ GagneB j t := by
  sorry

theorem pas_les_deux (j : Jeu) (t : Bool) : ¬(GagneA j t ∧ GagneB j t) := by
  sorry

end Parcours.Jeux

#verifier
