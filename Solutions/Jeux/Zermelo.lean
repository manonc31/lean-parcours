/- @parcours
titre: Le théorème de Zermelo
difficulte: 3
requiert: Jeux.Nim
indice: `zermelo` : récurrence sur le jeu `j` en généralisant le joueur `t` qui a le trait (`induction j generalizing t`), puis `cases t`.
indice: Si c'est à A de jouer dans `coup g d` : si A gagne dans `g` OU dans `d` (avec B au trait), A gagne. Sinon, B gagne dans `g` ET dans `d` (hypothèses de récurrence !), donc B gagne.
indice: `pas_les_deux` : récurrence sur `j` ; dans chaque cas, `cases` sur les deux hypothèses et utilise l'hypothèse de récurrence.
-/
import Solutions.Recurrence.Definitions

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

theorem zermelo (j : Jeu) (t : Bool) : GagneA j t ∨ GagneB j t := by -- @exo
  induction j generalizing t with
  | fin b =>
    cases b
    · exact Or.inr GagneB.fin
    · exact Or.inl GagneA.fin
  | coup g d ihg ihd =>
    cases t
    · rcases ihg true with hg | hg
      · rcases ihd true with hd | hd
        · exact Or.inl (GagneA.coup_B hg hd)
        · exact Or.inr (GagneB.coup_d hd)
      · exact Or.inr (GagneB.coup_g hg)
    · rcases ihg false with hg | hg
      · exact Or.inl (GagneA.coup_g hg)
      · rcases ihd false with hd | hd
        · exact Or.inl (GagneA.coup_d hd)
        · exact Or.inr (GagneB.coup_A hg hd)

theorem pas_les_deux (j : Jeu) (t : Bool) : ¬(GagneA j t ∧ GagneB j t) := by -- @exo
  induction j generalizing t with
  | fin b =>
    rintro ⟨ha, hb⟩
    cases ha
    cases hb
  | coup g d ihg ihd =>
    rintro ⟨ha, hb⟩
    cases ha with
    | coup_g hg =>
      cases hb with
      | coup_A hg' _ => exact ihg false ⟨hg, hg'⟩
    | coup_d hd =>
      cases hb with
      | coup_A _ hd' => exact ihd false ⟨hd, hd'⟩
    | coup_B hg hd =>
      cases hb with
      | coup_g hg' => exact ihg true ⟨hg, hg'⟩
      | coup_d hd' => exact ihd true ⟨hd, hd'⟩

end Parcours.Jeux

#verifier
