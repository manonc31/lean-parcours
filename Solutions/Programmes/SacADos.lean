/- @parcours
titre: Le sac à dos
difficulte: 3
requiert: Programmes.Monnaie
indice: Les deux théorèmes : récurrence sur la liste d'objets, en généralisant la capacité `c`.
indice: Un choix de `parties (x :: l)` est soit un choix de `parties l`, soit `x :: s'` ; dans le second cas, `s'` rentre dans un sac de capacité `c − w`.
indice: `omega` sait raisonner avec `max`.
-/
import Solutions.Programmes.Definitions

/-!
# Le sac à dos

Un cambrioleur a un sac qui supporte 10 kg. Quels objets emporter pour maximiser la valeur ?
La **programmation dynamique** (Bellman, années 1950) répond avec une équation : pour le premier
objet, soit on le laisse, soit on le prend (s'il rentre), et on garde le meilleur des deux.

On prouve que cette équation donne vraiment l'optimum : elle majore la valeur de **tout** choix
d'objets possible, et elle est atteinte.

## À prouver
1. `sac_majore` : aucun choix qui rentre dans le sac ne vaut plus que `sac l c`.
2. `sac_atteint` : il existe un choix qui atteint `sac l c`.
3. `cambriolage : sac objets 10 = 113`

## Ressources
- [Problème du sac à dos (Wikipédia)](https://fr.wikipedia.org/wiki/Probl%C3%A8me_du_sac_%C3%A0_dos)
-/

namespace Parcours.Prog

/-- Les objets sont des couples (poids, valeur). -/
def sac : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | (w, v) :: r, c => if w ≤ c then max (sac r c) (v + sac r (c - w)) else sac r c

def parties {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: l => parties l ++ (parties l).map (x :: ·)

def poidsSac (s : List (Nat × Nat)) : Nat := (s.map Prod.fst).sum
def valeurSac (s : List (Nat × Nat)) : Nat := (s.map Prod.snd).sum

theorem sac_majore (l : List (Nat × Nat)) (c : Nat) :
    ∀ s ∈ parties l, poidsSac s ≤ c → valeurSac s ≤ sac l c := by -- @exo
  induction l generalizing c with
  | nil =>
    intro s hs _
    simp [parties] at hs
    subst hs
    simp [valeurSac]
  | cons x l ih =>
    intro s hs hp
    obtain ⟨w, v⟩ := x
    simp only [parties, List.mem_append, List.mem_map] at hs
    simp only [sac]
    rcases hs with hs | ⟨s', hs', rfl⟩
    · have := ih c s hs hp
      split <;> omega
    · simp only [poidsSac, valeurSac, List.map_cons, List.sum_cons] at hp ⊢
      have := ih (c - w) s' hs' (by unfold poidsSac; omega)
      unfold valeurSac at this
      split <;> omega

theorem sac_atteint (l : List (Nat × Nat)) (c : Nat) :
    ∃ s ∈ parties l, poidsSac s ≤ c ∧ valeurSac s = sac l c := by -- @exo
  induction l generalizing c with
  | nil => exact ⟨[], by simp [parties], by simp [poidsSac], by simp [valeurSac, sac]⟩
  | cons x l ih =>
    obtain ⟨w, v⟩ := x
    obtain ⟨s1, h1, p1, v1⟩ := ih c
    simp only [sac]
    split
    · rename_i hw
      obtain ⟨s2, h2, p2, v2⟩ := ih (c - w)
      by_cases hm : sac l c ≤ v + sac l (c - w)
      · refine ⟨(w, v) :: s2, ?_, ?_, ?_⟩
        · simp only [parties, List.mem_append, List.mem_map]
          exact Or.inr ⟨s2, h2, rfl⟩
        · simp only [poidsSac, List.map_cons, List.sum_cons] at p2 ⊢
          omega
        · simp only [valeurSac, List.map_cons, List.sum_cons] at v2 ⊢
          omega
      · refine ⟨s1, ?_, p1, ?_⟩
        · simp only [parties, List.mem_append]
          exact Or.inl h1
        · omega
    · refine ⟨s1, ?_, p1, v1⟩
      simp only [parties, List.mem_append]
      exact Or.inl h1

def objets : List (Nat × Nat) := [(5, 10), (4, 40), (6, 30), (3, 50), (2, 15), (1, 8)]

theorem cambriolage : sac objets 10 = 113 := by -- @exo
  decide

end Parcours.Prog

#verifier
