import Exercices.Graphes.Definitions

/-!
# Les ponts de Königsberg

La ville de Königsberg (aujourd'hui Kaliningrad) a 7 ponts reliant 4 quartiers. Peut-on faire
une promenade qui traverse **chaque pont exactement une fois** ? En 1736, Euler prouve que non,
et invente au passage la théorie des graphes. (Numéro 54 de la liste des « 100 théorèmes ».)

L'argument d'Euler : sur une promenade, chaque passage par un quartier utilise **deux** ponts
(un pour arriver, un pour repartir). Seuls le départ et l'arrivée peuvent avoir un nombre impair
de ponts. Or à Königsberg, les **quatre** quartiers ont un nombre impair de ponts (5, 3, 3, 3).

Une **piste** de `v` à `w` qui utilise les arêtes de `g` (chacune une fois, dans l'ordre) :
`Piste g v w`. « Chaque pont exactement une fois » : la liste des arêtes de la piste est une
**permutation** de celle du graphe.

## À prouver
1. `degres_impairs` : les 4 sommets de Königsberg sont de degré impair.
2. `parite_piste` : le lemme de parité d'Euler.
3. `konigsberg_impossible : ¬∃ g v w, g.Perm konigsberg ∧ Piste g v w`

## Ressources
- [Problème des sept ponts de Königsberg (Wikipédia)](https://fr.wikipedia.org/wiki/Probl%C3%A8me_des_sept_ponts_de_K%C3%B6nigsberg)

---
*Exercice* `Graphes.Konigsberg` · difficulté ★★★★☆

💡 Indices : `./parcours indice Graphes.Konigsberg` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Graphes

/-- Les 7 ponts : 0 = l'île de Kneiphof, 1 = rive nord, 2 = rive sud, 3 = l'est. -/
def konigsberg : Graphe := [(0, 1), (0, 1), (0, 2), (0, 2), (0, 3), (1, 3), (2, 3)]

/-- Une piste de `v` à `w` utilisant exactement les arêtes de la liste (dans l'ordre). -/
inductive Piste : Graphe → Nat → Nat → Prop
  | vide (v : Nat) : Piste [] v v
  | etape {g : Graphe} {v x w : Nat} (e : Nat × Nat) :
      (e = (v, x) ∨ e = (x, v)) → Piste g x w → Piste (e :: g) v w

theorem degres_impairs : (List.range 4).all (fun v => degre konigsberg v % 2 == 1) = true := by
  sorry

theorem parite_piste {g : Graphe} {v w : Nat} (hp : Piste g v w) (u : Nat) :
    (degre g u + (if u = v then 1 else 0) + (if u = w then 1 else 0)) % 2 = 0 := by
  sorry

theorem konigsberg_impossible : ¬∃ g v w, g.Perm konigsberg ∧ Piste g v w := by
  sorry

end Parcours.Graphes

#verifier
