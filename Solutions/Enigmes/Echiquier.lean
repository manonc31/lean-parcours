/- @parcours
titre: L'échiquier mutilé
difficulte: 4
requiert: Tris.Coherence
indice: Colorie l'échiquier : la case `(i, j)` est blanche si `i + j` est pair. Deux cases adjacentes sont de couleurs différentes, donc **chaque domino couvre exactement une case blanche**.
indice: Lemme : `((dominos.flatMap (fun d => [d.1, d.2])).countP blanche) = dominos.length`, par récurrence sur `dominos` (`List.flatMap_cons`, `List.countP_append`).
indice: Idem pour les cases noires. Or le plateau a 30 cases blanches et 32 noires (`decide`), et une permutation préserve les comptages (`List.Perm.countP_eq`). Contradiction : `30 = 32`.
-/
import Solutions.Tris.Definitions

/-!
# L'échiquier mutilé

On retire deux coins **opposés** d'un échiquier 8×8. Peut-on recouvrir les 62 cases restantes
avec 31 dominos (chaque domino couvre deux cases adjacentes) ?

Non ! Et la preuve tient en une idée : les deux coins retirés sont de la **même couleur**.
Un ordinateur qui chercherait par force brute mettrait un temps astronomique ; un argument de
coloriage règle la question. (Problème de Max Black, 1946, popularisé par Martin Gardner.)

Un pavage est une liste de dominos `(c, d)` de cases adjacentes, qui couvre chaque case
**exactement une fois** : la liste de toutes les cases couvertes est une **permutation** du plateau.

## À prouver
`echiquier_mutile : (∀ d ∈ dominos, Adjacentes d.1 d.2) → (dominos.flatMap (fun d => [d.1, d.2])).Perm plateau → False`

## Ressources
- [Problème de l'échiquier mutilé (Wikipédia)](https://fr.wikipedia.org/wiki/Probl%C3%A8me_de_l%27%C3%A9chiquier_mutil%C3%A9)
-/

namespace Parcours.Enigmes

abbrev Case := Nat × Nat

/-- Les 62 cases : l'échiquier 8×8 privé des coins (0,0) et (7,7). -/
def plateau : List Case :=
  ((List.range 8).flatMap fun i => (List.range 8).map fun j => (i, j)).filter
    (fun c => c != (0, 0) && c != (7, 7))

def Adjacentes (c d : Case) : Prop :=
  (c.1 = d.1 ∧ (c.2 + 1 = d.2 ∨ d.2 + 1 = c.2)) ∨ (c.2 = d.2 ∧ (c.1 + 1 = d.1 ∨ d.1 + 1 = c.1))

def blanche (c : Case) : Bool := (c.1 + c.2) % 2 == 0

theorem compte (dominos : List (Case × Case)) (hadj : ∀ d ∈ dominos, Adjacentes d.1 d.2)
    (p : Case → Bool) (hp : ∀ c d, Adjacentes c d → p c = !p d) :
    (dominos.flatMap (fun d => [d.1, d.2])).countP p = dominos.length := by -- @exo
  induction dominos with
  | nil => rfl
  | cons d ds ih =>
    rw [List.flatMap_cons, List.countP_append, ih (fun e he => hadj e (List.mem_cons_of_mem d he))]
    have h := hp d.1 d.2 (hadj d List.mem_cons_self)
    simp only [List.length_cons]
    cases h1 : p d.2 <;> simp [h, h1] <;> omega

theorem echiquier_mutile (dominos : List (Case × Case)) (hadj : ∀ d ∈ dominos, Adjacentes d.1 d.2)
    (hpavage : (dominos.flatMap (fun d => [d.1, d.2])).Perm plateau) : False := by -- @exo
  have hb : ∀ c d, Adjacentes c d → blanche c = !blanche d := by
    intro c d h
    unfold Adjacentes at h
    unfold blanche
    rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩ <;>
      · cases hc : ((c.1 + c.2) % 2 == 0) <;> cases hd : ((d.1 + d.2) % 2 == 0) <;> simp_all <;> omega
  have hn : ∀ c d, Adjacentes c d → (!blanche c) = !(!blanche d) := by
    intro c d h
    rw [hb c d h]
  have e1 := hpavage.countP_eq blanche
  have e2 := hpavage.countP_eq (fun c => !blanche c)
  rw [compte dominos hadj _ hb] at e1
  rw [compte dominos hadj _ hn] at e2
  have p1 : plateau.countP blanche = 30 := by decide
  have p2 : plateau.countP (fun c => !blanche c) = 32 := by decide
  omega

end Parcours.Enigmes

#verifier
