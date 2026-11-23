import Exercices.Algorithmes.Definitions

/-!
# La compression RLE

« Run-length encoding » : `[5, 5, 5, 2, 2, 7]` devient `[(5, 3), (2, 2), (7, 1)]`
(la valeur, puis combien de fois elle se répète). C'est l'une des plus vieilles méthodes de
compression (fax, images BMP, PCX…). Un compresseur doit être **sans perte** : décompresser
redonne exactement l'original. Prouve-le !

## À prouver
`decoder_encoder (l : List Nat) : decoder (encoder l) = l`

## Ressources
- [Run-length encoding (Wikipédia)](https://fr.wikipedia.org/wiki/Run-length_encoding)

---
*Exercice* `Algorithmes.RLE` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Algorithmes.RLE` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Algo

def encoder : List Nat → List (Nat × Nat)
  | [] => []
  | x :: l =>
    match encoder l with
    | (y, k) :: r => if x = y then (y, k + 1) :: r else (x, 1) :: (y, k) :: r
    | [] => [(x, 1)]

def decoder (l : List (Nat × Nat)) : List Nat := l.flatMap (fun p => List.replicate p.2 p.1)

example : encoder [5, 5, 5, 2, 2, 7] = [(5, 3), (2, 2), (7, 1)] := by decide

theorem decoder_encoder (l : List Nat) : decoder (encoder l) = l := by
  sorry

end Parcours.Algo

#verifier
