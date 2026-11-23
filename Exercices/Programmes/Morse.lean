import Exercices.Programmes.Definitions

/-!
# Le code Morse

Le code Morse (1838) code chaque lettre par des points et des traits : `E = ·`, `T = −`,
`S = · · ·`, `O = − − −`. Les lettres fréquentes ont des codes courts.

Attention : sans les espaces entre lettres, on ne peut pas décoder ! `E E = · · = I`.

On code les lettres par des nombres (`A = 0`, …, `Z = 25`) et `false = ·`, `true = −`.

## À prouver
1. `lettre_morse` : chaque lettre se décode correctement.
2. `decoder_coder` : un mot codé lettre par lettre se décode en le mot de départ.
3. `ambigu : morse 4 ++ morse 4 = morse 8` (« EE » collés = « I »).

## Ressources
- [Code Morse international (Wikipédia)](https://fr.wikipedia.org/wiki/Code_Morse_international)

---
*Exercice* `Programmes.Morse` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Programmes.Morse` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

def tableMorse : List (List Bool) :=
  [[false, true], [true, false, false, false], [true, false, true, false], [true, false, false],
   [false], [false, false, true, false], [true, true, false], [false, false, false, false],
   [false, false], [false, true, true, true], [true, false, true], [false, true, false, false],
   [true, true], [true, false], [true, true, true], [false, true, true, false],
   [true, true, false, true], [false, true, false], [false, false, false], [true],
   [false, false, true], [false, false, false, true], [false, true, true], [true, false, false, true],
   [true, false, true, true], [true, true, false, false]]

def morse (c : Nat) : List Bool := tableMorse.getD c []

def lettre (code : List Bool) : Option Nat := (List.range 26).find? fun c => morse c == code

def decoder : List (List Bool) → Option (List Nat)
  | [] => some []
  | x :: r =>
    match lettre x, decoder r with
    | some c, some w => some (c :: w)
    | _, _ => none

theorem lettre_morse : ∀ c, c < 26 → lettre (morse c) = some c := by
  sorry

theorem decoder_coder (w : List Nat) (h : ∀ c ∈ w, c < 26) : decoder (w.map morse) = some w := by
  sorry

theorem ambigu : morse 4 ++ morse 4 = morse 8 := by
  sorry

end Parcours.Prog

#verifier
