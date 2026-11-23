/- @parcours
titre: Les ponts de Königsberg
difficulte: 4
celebre: 54
indice: Le lemme clé (parité) : pour une piste de `v` à `w` utilisant les arêtes `g`, et pour tout sommet `u`, `(degre g u + [u = v] + [u = w])` est pair. Récurrence sur la piste (`induction hp with`).
indice: Dans le cas `etape`, l'arête est `(v, x)` ou `(x, v)` : `rcases he with rfl | rfl`, puis `simp only [degre, extremites_cons, List.count_cons, beq_iff_eq] at ih ⊢`. Il reste des `if` : `split` (et `split at ih`) les découpe tous, puis `omega`.
indice: Pour Königsberg : les degrés sont 5, 3, 3, 3 (`decide`). Une permutation des arêtes ne change pas les degrés (`List.Perm.flatMap_right` puis `List.Perm.count_eq`). Parmi les sommets 0, 1, 2, l'un n'est ni `v` ni `w` : son degré devrait être pair.
-/
import Solutions.Graphes.Definitions

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
-/

namespace Parcours.Graphes

/-- Les 7 ponts : 0 = l'île de Kneiphof, 1 = rive nord, 2 = rive sud, 3 = l'est. -/
def konigsberg : Graphe := [(0, 1), (0, 1), (0, 2), (0, 2), (0, 3), (1, 3), (2, 3)]

/-- Une piste de `v` à `w` utilisant exactement les arêtes de la liste (dans l'ordre). -/
inductive Piste : Graphe → Nat → Nat → Prop
  | vide (v : Nat) : Piste [] v v
  | etape {g : Graphe} {v x w : Nat} (e : Nat × Nat) :
      (e = (v, x) ∨ e = (x, v)) → Piste g x w → Piste (e :: g) v w

theorem degres_impairs : (List.range 4).all (fun v => degre konigsberg v % 2 == 1) = true := by -- @exo
  decide

theorem parite_piste {g : Graphe} {v w : Nat} (hp : Piste g v w) (u : Nat) :
    (degre g u + (if u = v then 1 else 0) + (if u = w then 1 else 0)) % 2 = 0 := by -- @exo
  induction hp with
  | vide v =>
    simp only [degre, extremites, List.flatMap_nil, List.count_nil]
    split <;> omega
  | @etape g v x w e he _ ih =>
    rcases he with rfl | rfl
    · simp only [degre, extremites_cons, List.count_cons, beq_iff_eq] at ih ⊢
      repeat' split
      all_goals (repeat' split at ih)
      all_goals omega
    · simp only [degre, extremites_cons, List.count_cons, beq_iff_eq] at ih ⊢
      repeat' split
      all_goals (repeat' split at ih)
      all_goals omega

theorem konigsberg_impossible : ¬∃ g v w, g.Perm konigsberg ∧ Piste g v w := by -- @exo
  rintro ⟨g, v, w, hperm, hp⟩
  have hdeg : ∀ u, degre g u = degre konigsberg u := fun u =>
    (hperm.flatMap_right (fun e : Nat × Nat => [e.1, e.2])).count_eq u
  have h0 : degre konigsberg 0 = 5 := by decide
  have h1 : degre konigsberg 1 = 3 := by decide
  have h2 : degre konigsberg 2 = 3 := by decide
  have p0 := parite_piste hp 0
  have p1 := parite_piste hp 1
  have p2 := parite_piste hp 2
  rw [hdeg] at p0 p1 p2
  rw [h0] at p0
  rw [h1] at p1
  rw [h2] at p2
  repeat' split at p0
  all_goals (repeat' split at p1)
  all_goals (repeat' split at p2)
  all_goals omega

end Parcours.Graphes

#verifier
