import Exercices.Recurrence.Definitions

/-!
# Curiosités du calcul

Quelques calculs étonnants :
- `37 × 3 = 111`, `37 × 6 = 222`, …, `37 × 27 = 999` ;
- `12345679 × 9 = 111111111` (sans le 8 !) ;
- `111111111² = 12345678987654321` ;
- `1089 × 9 = 9801` et `2178 × 4 = 8712` : le produit est le nombre **retourné**.

On peut les vérifier un par un par le calcul (`decide`)… mais pour « 37 × 3k = 111k » on peut
aussi prouver la règle **générale**, pour tout `k`.

## À prouver
`trente_sept`, `trente_sept_general`, `repunit_carre`, `sans_huit`, `retournes`.

---
*Exercice* `Enigmes.Curiosites` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Enigmes.Curiosites` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Enigmes

theorem trente_sept : ∀ k, k < 10 → 37 * (3 * k) = 111 * k := by
  sorry

theorem trente_sept_general (k : Nat) : 37 * (3 * k) = 111 * k := by
  sorry

theorem repunit_carre : 111111111 * 111111111 = 12345678987654321 := by
  sorry

theorem sans_huit : 12345679 * 9 = 111111111 := by
  sorry

theorem retournes : 1089 * 9 = 9801 ∧ 2178 * 4 = 8712 := by
  sorry

end Parcours.Enigmes

#verifier
