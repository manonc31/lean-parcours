/- @parcours
titre: Les dés non transitifs d'Efron
difficulte: 2
requiert: Probabilites.Des
indice: Un calcul sur 4 × 36 issues : `decide`.
-/
import Solutions.Probabilites.Definitions

/-!
# Les dés non transitifs d'Efron

Quatre dés étranges :
- A : `4 4 4 4 0 0` ;
- B : `3 3 3 3 3 3` ;
- C : `6 6 2 2 2 2` ;
- D : `5 5 5 1 1 1`.

A bat B deux fois sur trois, B bat C deux fois sur trois, C bat D deux fois sur trois… et **D bat A**
deux fois sur trois ! « Être plus fort que » n'est pas transitif. (Bradley Efron, 1970 ; Warren Buffett
aurait proposé ce jeu à Bill Gates, qui a flairé le piège et laissé Buffett choisir son dé en premier.)

## À prouver
`efron` : les quatre duels sont gagnés avec probabilité 2/3.
-/

namespace Parcours.Proba

def deA : List Nat := [4, 4, 4, 4, 0, 0]
def deB : List Nat := [3, 3, 3, 3, 3, 3]
def deC : List Nat := [6, 6, 2, 2, 2, 2]
def deD : List Nat := [5, 5, 5, 1, 1, 1]

/-- Toutes les issues d'un duel entre deux dés. -/
def duel (x y : List Nat) : List (Nat × Nat) := x.flatMap (fun a => y.map (fun b => (a, b)))

def gagne (p : Nat × Nat) : Bool := decide (p.2 < p.1)

theorem efron : ProbaEst (duel deA deB) gagne 2 3 ∧ ProbaEst (duel deB deC) gagne 2 3 ∧
    ProbaEst (duel deC deD) gagne 2 3 ∧ ProbaEst (duel deD deA) gagne 2 3 := by -- @exo
  decide

end Parcours.Proba

#verifier
