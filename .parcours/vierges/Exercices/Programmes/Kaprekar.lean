import Exercices.Programmes.Definitions

/-!
# La constante de Kaprekar

Prends un nombre à 3 chiffres (pas tous égaux), range ses chiffres dans l'ordre décroissant
puis croissant, et soustrais : `352 → 532 − 235 = 297 → 972 − 279 = 693 → 963 − 369 = 594 →
954 − 459 = 495 → 954 − 459 = 495`… On tombe **toujours** sur 495 ! (Avec 4 chiffres, c'est
6174 : 7641 − 1467 = 6174.)

Astuce : `grand − petit = 100a + 10b + c − (100c + 10b + a) = 99 × (a − c)` si `a` est le plus
grand chiffre et `c` le plus petit.

## À prouver
1. `kaprekar_495` : pour tout nombre de 0 à 999 dont les chiffres ne sont pas tous égaux,
   6 étapes suffisent pour arriver à 495.
2. `fixe_495 : kaprekar 495 = 495`

## Ressources
- [Algorithme de Kaprekar (Wikipédia)](https://fr.wikipedia.org/wiki/Algorithme_de_Kaprekar)

---
*Exercice* `Programmes.Kaprekar` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Programmes.Kaprekar` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

def kaprekar (n : Nat) : Nat :=
  let a := n / 100
  let b := n / 10 % 10
  let c := n % 10
  99 * (max a (max b c) - min a (min b c))

theorem fixe_495 : kaprekar 495 = 495 := by
  sorry

theorem kaprekar_495 : ∀ n, n < 1000 → (n / 100 ≠ n / 10 % 10 ∨ n / 10 % 10 ≠ n % 10) →
    repeter kaprekar 6 n = 495 := by
  sorry

end Parcours.Prog

#verifier
