/- @parcours
titre: Le triangle de Pascal en listes
difficulte: 2
requiert: Programmes.Accumulateur
indice: `somme_zipWith` : récurrence sur `a` en généralisant `b`, puis `cases b`.
indice: Pour `somme_pascal` : la somme de `0 :: l` et de `l ++ [0]` vaut deux fois celle de `l`.
-/
import Solutions.Programmes.Definitions

/-!
# Le triangle de Pascal en listes

Chaque ligne du triangle de Pascal s'obtient en additionnant la ligne précédente décalée et
la ligne précédente : `[1, 3, 3, 1]` → `[0, 1, 3, 3, 1] + [1, 3, 3, 1, 0] = [1, 4, 6, 4, 1]`.
Conséquence : la somme double à chaque ligne, donc la ligne `n` a pour somme `2^n`.

## À prouver
1. `somme_zipWith` : la somme de deux listes additionnées terme à terme.
2. `longueur_pascal : (pascal n).length = n + 1`
3. `somme_pascal : (pascal n).sum = 2 ^ n`
4. `ligne_quatre : pascal 4 = [1, 4, 6, 4, 1]`

## Ressources
- [Triangle de Pascal (Wikipédia)](https://fr.wikipedia.org/wiki/Triangle_de_Pascal)
-/

namespace Parcours.Prog

def ligneSuivante (l : List Nat) : List Nat := List.zipWith (· + ·) (0 :: l) (l ++ [0])

def pascal : Nat → List Nat
  | 0 => [1]
  | n + 1 => ligneSuivante (pascal n)

theorem somme_zipWith (a b : List Nat) (h : a.length = b.length) :
    (List.zipWith (· + ·) a b).sum = a.sum + b.sum := by -- @exo
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons x a ih =>
    cases b with
    | nil => simp at h
    | cons y b =>
      simp only [List.zipWith_cons_cons, List.sum_cons, ih b (by simpa using h)]
      omega

theorem longueur_pascal (n : Nat) : (pascal n).length = n + 1 := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih => simp [pascal, ligneSuivante, ih]

theorem somme_pascal (n : Nat) : (pascal n).sum = 2 ^ n := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pascal, ligneSuivante]
    rw [somme_zipWith _ _ (by simp)]
    simp [ih, Nat.pow_succ]
    omega

theorem ligne_quatre : pascal 4 = [1, 4, 6, 4, 1] := by -- @exo
  decide

end Parcours.Prog

#verifier
