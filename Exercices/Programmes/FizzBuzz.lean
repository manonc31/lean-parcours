import Exercices.Programmes.Definitions

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

---
*Exercice* `Programmes.FizzBuzz` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Programmes.FizzBuzz` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
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

theorem fb_quinze (k : Nat) : fb (15 * k) = .fizzbuzz := by
  sorry

theorem fb_fizz (n : Nat) : fb n = .fizz ↔ n % 3 = 0 ∧ n % 5 ≠ 0 := by
  sorry

theorem fizz_cent : ((List.range 100).filter (fun n => fb (n + 1) = .fizz)).length = 27 := by
  sorry

end Parcours.Prog

#verifier
