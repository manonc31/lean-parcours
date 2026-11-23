/- @parcours
titre: Curiosités du calcul
difficulte: 1
requiert: Enigmes.Nombre1089
indice: Pour les calculs : `decide`. Pour la règle générale : `omega`.
-/
import Solutions.Recurrence.Definitions

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
-/

namespace Parcours.Enigmes

theorem trente_sept : ∀ k, k < 10 → 37 * (3 * k) = 111 * k := by -- @exo
  decide

theorem trente_sept_general (k : Nat) : 37 * (3 * k) = 111 * k := by -- @exo
  omega

theorem repunit_carre : 111111111 * 111111111 = 12345678987654321 := by -- @exo
  decide

theorem sans_huit : 12345679 * 9 = 111111111 := by -- @exo
  decide

theorem retournes : 1089 * 9 = 9801 ∧ 2178 * 4 = 8712 := by -- @exo
  decide

end Parcours.Enigmes

#verifier
