/- @parcours
titre: Le mot de Thue-Morse
difficulte: 2
requiert: Programmes.Pascal
indice: `longueur_thue` : récurrence, `List.length_append`, `List.length_map`, `Nat.pow_succ`.
indice: `prefixe` : `List.prefix_append`.
indice: `sans_cube` : un calcul, `decide +kernel`.
-/
import Solutions.Programmes.Definitions

/-!
# Le mot de Thue-Morse

On part de `0`, et à chaque étape on recopie le mot en ajoutant à la suite son « négatif » :
`0 → 01 → 0110 → 01101001 → …`. Ce mot étrange apparaît partout : partage équitable (pour choisir
des équipes, A B B A B A A B est plus juste que A B A B…), échecs (règle de nullité infinie),
fractales…

Une de ses propriétés étonnantes : il ne contient jamais trois fois de suite le même bloc
(« sans cube »).

## À prouver
1. `longueur_thue : (thue n).length = 2 ^ n`
2. `prefixe : thue n <+: thue (n + 1)` (chaque mot prolonge le précédent)
3. `sans_cube` : `thue 5` (32 lettres) ne contient aucun bloc répété trois fois de suite.

## Ressources
- [Suite de Prouhet-Thue-Morse (Wikipédia)](https://fr.wikipedia.org/wiki/Suite_de_Prouhet-Thue-Morse)
-/

namespace Parcours.Prog

def thue : Nat → List Bool
  | 0 => [false]
  | n + 1 => thue n ++ (thue n).map (!·)

/-- Le mot `w` contient-il un bloc `u` (non vide) suivi de `u` puis encore de `u` ? -/
def aUnCube (w : List Bool) : Bool :=
  (List.range w.length).any fun i => (List.range w.length).any fun k =>
    let u := (w.drop i).take (k + 1)
    i + 3 * (k + 1) ≤ w.length &&
      (w.drop (i + k + 1)).take (k + 1) == u && (w.drop (i + 2 * (k + 1))).take (k + 1) == u

theorem longueur_thue (n : Nat) : (thue n).length = 2 ^ n := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [thue, List.length_append, List.length_map, ih, Nat.pow_succ]
    omega

theorem prefixe (n : Nat) : thue n <+: thue (n + 1) := by -- @exo
  exact List.prefix_append _ _

theorem sans_cube : aUnCube (thue 5) = false := by -- @exo
  decide +kernel

end Parcours.Prog

#verifier
