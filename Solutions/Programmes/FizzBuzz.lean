/- @parcours
titre: FizzBuzz
difficulte: 1
requiert: Programmes.Definitions
indice: `fb_quinze` : `simp [fb]` sait que `15 * k % 15 = 0`.
indice: `fb_fizz` : `unfold fb`, puis `repeat' split` pour casser tous les `if` ; dans chaque cas `simp` puis `omega`.
indice: `fizz_cent` : c'est un calcul, `decide`.
-/
import Solutions.Programmes.Definitions

/-!
# FizzBuzz

Le célèbre test d'entretien d'embauche : pour chaque nombre, afficher « Fizz » s'il est multiple
de 3, « Buzz » s'il est multiple de 5, « FizzBuzz » s'il est multiple des deux, et le nombre sinon.
Ici, la sortie est un petit type `Sortie` plutôt qu'une chaîne de caractères.

## À prouver
1. `fb_quinze : fb (15 * k) = .fizzbuzz`
2. `fb_fizz : fb n = .fizz ↔ n % 3 = 0 ∧ n % 5 ≠ 0`
3. `fizz_cent` : entre 1 et 100, il y a exactement 27 « Fizz ».

## Ressources
- [FizzBuzz (Rosetta Code)](https://rosettacode.org/wiki/FizzBuzz)
-/

namespace Parcours.Prog

inductive Sortie where
  | fizz
  | buzz
  | fizzbuzz
  | nombre (n : Nat)
  deriving DecidableEq

def fb (n : Nat) : Sortie :=
  if n % 15 = 0 then .fizzbuzz
  else if n % 3 = 0 then .fizz
  else if n % 5 = 0 then .buzz
  else .nombre n

theorem fb_quinze (k : Nat) : fb (15 * k) = .fizzbuzz := by -- @exo
  simp [fb]

theorem fb_fizz (n : Nat) : fb n = .fizz ↔ n % 3 = 0 ∧ n % 5 ≠ 0 := by -- @exo
  unfold fb
  repeat' split
  all_goals simp
  all_goals omega

theorem fizz_cent : ((List.range 100).filter (fun n => fb (n + 1) = .fizz)).length = 27 := by -- @exo
  decide

end Parcours.Prog

#verifier
