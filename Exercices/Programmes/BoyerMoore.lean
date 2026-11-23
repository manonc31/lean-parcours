import Exercices.Programmes.Definitions

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

---
*Exercice* `Programmes.BoyerMoore` · difficulté ★★★★☆

💡 Indices : `./parcours indice Programmes.BoyerMoore` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
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
    B + (if y = x then 1 else -1) ≤ borne (pasBM c k y).1 (pasBM c k y).2 x := by
  sorry

theorem bal_cons (x y : Nat) (l : List Nat) : bal x (y :: l) = bal x l + (if y = x then 1 else -1) := by
  sorry

theorem bm_inv (l : List Nat) : ∀ (c k x : Nat) (B : Int), B ≤ borne c k x →
    B + bal x l ≤ borne (bm l c k).1 (bm l c k).2 x := by
  sorry

theorem majorite (l : List Nat) (m c : Nat) (h : l.length < 2 * l.count m) : (bm l c 0).1 = m := by
  sorry

end Parcours.Prog

#verifier
