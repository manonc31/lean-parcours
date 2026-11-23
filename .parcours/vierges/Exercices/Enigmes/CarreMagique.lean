import Exercices.Recurrence.Definitions

/-!
# Le carré magique

Un carré magique 3×3 contient les nombres 1 à 9, et toutes les lignes, colonnes et diagonales
ont la même somme (forcément 15, puisque 1 + ⋯ + 9 = 45 = 3 × 15). Le plus ancien connu est le
*Lo Shu* chinois (vers 650 av. J.-C.) :

```
4 9 2
3 5 7
8 1 6
```

## À prouver
1. `lo_shu` : c'est bien un carré magique.
2. `centre_cinq` : dans **tout** carré magique 3×3 (de somme totale 45), le centre vaut 5.

## Ressources
- [Carré magique (Wikipédia)](https://fr.wikipedia.org/wiki/Carr%C3%A9_magique_%28math%C3%A9matiques%29)

---
*Exercice* `Enigmes.CarreMagique` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Enigmes.CarreMagique` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Enigmes

def Magique (a b c d e f g h i : Nat) : Prop :=
  a + b + c = 15 ∧ d + e + f = 15 ∧ g + h + i = 15 ∧
  a + d + g = 15 ∧ b + e + h = 15 ∧ c + f + i = 15 ∧
  a + e + i = 15 ∧ c + e + g = 15

instance (a b c d e f g h i : Nat) : Decidable (Magique a b c d e f g h i) := by
  unfold Magique; infer_instance

theorem lo_shu : Magique 4 9 2 3 5 7 8 1 6 := by
  sorry

theorem centre_cinq (a b c d e f g h i : Nat) (hm : Magique a b c d e f g h i)
    (htot : a + b + c + d + e + f + g + h + i = 45) : e = 5 := by
  sorry

end Parcours.Enigmes

#verifier
