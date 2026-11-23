/- @parcours
titre: Le vote majoritaire de Boyer-Moore
difficulte: 4
requiert: Programmes.Compter
indice: `pas_inv` : beaucoup de cas (compteur nul ou non, candidat égal à `y` ou non, `x` égal au candidat ou à `y`…) ; dans chacun, `simp only [h…, ↓reduceIte]` puis `omega`.
indice: `bm_inv` : récurrence sur `l` en généralisant tout ; la borne de départ `B` absorbe ce qui a déjà été lu.
indice: `majorite` : applique `bm_inv` avec `B = 0` et un compteur nul au départ.
-/
import Solutions.Programmes.Definitions

/-!
# Le vote majoritaire de Boyer-Moore

Comment trouver l'élément **majoritaire** d'une liste (présent plus d'une fois sur deux) en un
seul passage et avec une mémoire minuscule ? L'algorithme de Boyer et Moore (1981) garde un
**candidat** et un **compteur** : un élément égal au candidat fait monter le compteur, un élément
différent le fait baisser (il « annule » une voix du candidat) ; à 0, on change de candidat.

## L'invariant
Pour chaque valeur `x`, note `bal x` = (nombre de `x`) − (nombre d'autres éléments) dans la partie
déjà lue. Alors à tout moment : `bal x ≤ k` si `x` est le candidat, et `bal x ≤ −k` sinon.
À la fin, si `m` est majoritaire, `bal m > 0`, donc `m` est forcément le candidat !

## À prouver
1. `pas_inv` : un pas de l'algorithme préserve l'invariant.
2. `bal_cons`, `bm_inv` : l'invariant à la fin.
3. `majorite : l.length < 2 * l.count m → (bm l c 0).1 = m`

## Ressources
- [Algorithme de vote à la majorité de Boyer-Moore (Wikipédia)](https://fr.wikipedia.org/wiki/Algorithme_de_vote_%C3%A0_la_majorit%C3%A9_de_Boyer-Moore)
-/

namespace Parcours.Prog

def pasBM (c k y : Nat) : Nat × Nat :=
  if k = 0 then (y, 1) else if c = y then (c, k + 1) else (c, k - 1)

def bm : List Nat → Nat → Nat → Nat × Nat
  | [], c, k => (c, k)
  | y :: l, c, k => bm l (pasBM c k y).1 (pasBM c k y).2

def bal (x : Nat) (l : List Nat) : Int := 2 * (l.count x : Int) - l.length

def borne (c k x : Nat) : Int := if c = x then (k : Int) else -(k : Int)

theorem pas_inv (c k y x : Nat) (B : Int) (h : B ≤ borne c k x) :
    B + (if y = x then 1 else -1) ≤ borne (pasBM c k y).1 (pasBM c k y).2 x := by -- @exo
  unfold borne pasBM at *
  by_cases hk : k = 0
  · simp only [hk, ↓reduceIte] at h ⊢
    by_cases hyx : y = x <;> simp only [hyx, ↓reduceIte] <;> split at h <;> omega
  · simp only [hk, ↓reduceIte]
    by_cases hcy : c = y
    · subst hcy
      by_cases hcx : c = x <;> simp only [hcx, ↓reduceIte] at h ⊢ <;> omega
    · simp only [hcy, ↓reduceIte]
      by_cases hcx : c = x <;> by_cases hyx : y = x <;> simp only [hcx, hyx, ↓reduceIte] at h ⊢ <;> omega

theorem bal_cons (x y : Nat) (l : List Nat) : bal x (y :: l) = bal x l + (if y = x then 1 else -1) := by -- @exo
  unfold bal
  rw [List.count_cons, List.length_cons]
  by_cases h : y = x <;> simp [h] <;> omega

theorem bm_inv (l : List Nat) : ∀ (c k x : Nat) (B : Int), B ≤ borne c k x →
    B + bal x l ≤ borne (bm l c k).1 (bm l c k).2 x := by -- @exo
  induction l with
  | nil =>
    intro c k x B h
    simpa [bm, bal] using h
  | cons y l ih =>
    intro c k x B h
    have := ih (pasBM c k y).1 (pasBM c k y).2 x _ (pas_inv c k y x B h)
    rw [bal_cons]
    simp only [bm]
    omega

theorem majorite (l : List Nat) (m c : Nat) (h : l.length < 2 * l.count m) : (bm l c 0).1 = m := by -- @exo
  have := bm_inv l c 0 m 0 (by simp [borne])
  unfold bal borne at this
  by_cases hne : (bm l c 0).1 = m
  · exact hne
  · simp only [hne, ↓reduceIte] at this
    omega

end Parcours.Prog

#verifier
