import Exercices.Listes.Pont
import Exercices.Recurrence.Definitions

/-!
# Le jeu de 24

Avec quatre cartes, obtenir 24 en utilisant chaque carte exactement une fois et les opérations
`+ − × ÷` (divisions exactes seulement). Par exemple, avec 1, 2, 3, 4 : `1 × 2 × 3 × 4 = 24`.

## À faire
Écris les calculs `partie1` à `partie4`, pour les cartes :
1. `[4, 7, 8, 8]`
2. `[3, 3, 3, 3]`
3. `[5, 5, 5, 5]`
4. `[10, 10, 4, 4]`
puis prouve `tout_reussi`.

## Ressources
- [Jeu de 24 (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/24_(puzzle))

---
*Exercice* `Enigmes.Jeu24` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Enigmes.Jeu24` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Enigmes

inductive Calcul where
  | nb (k : Nat)
  | plus (a b : Calcul)
  | moins (a b : Calcul)
  | fois (a b : Calcul)
  | divise (a b : Calcul)

def Calcul.val : Calcul → Option Nat
  | .nb k => some k
  | .plus a b => do return (← a.val) + (← b.val)
  | .moins a b => do
    let x ← a.val
    let y ← b.val
    if y ≤ x then some (x - y) else none
  | .fois a b => do return (← a.val) * (← b.val)
  | .divise a b => do
    let x ← a.val
    let y ← b.val
    if y ≠ 0 ∧ x % y = 0 then some (x / y) else none

def Calcul.cartes : Calcul → List Nat
  | .nb k => [k]
  | .plus a b => a.cartes ++ b.cartes
  | .moins a b => a.cartes ++ b.cartes
  | .fois a b => a.cartes ++ b.cartes
  | .divise a b => a.cartes ++ b.cartes

def Reussi (c : Calcul) (main : List Nat) : Bool := c.val == some 24 && c.cartes.isPerm main

open Calcul in
def partie1 : Calcul :=
  sorry

open Calcul in
def partie2 : Calcul :=
  sorry

open Calcul in
def partie3 : Calcul :=
  sorry

open Calcul in
def partie4 : Calcul :=
  sorry

theorem tout_reussi : Reussi partie1 [4, 7, 8, 8] && Reussi partie2 [3, 3, 3, 3] &&
    Reussi partie3 [5, 5, 5, 5] && Reussi partie4 [10, 10, 4, 4] = true := by
  sorry

end Parcours.Enigmes

#verifier
