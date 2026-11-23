import Exercices.Logique.Bilan
import Exercices.Naturels.Transfert

/-!
# Existence et unicité

« Il existe **un et un seul** `x` tel que `p x` » : on le définit comme
`ExisteUnique p := ∃ x, p x ∧ ∀ y, p y → y = x` (Mathlib le note `∃! x, p x`).

## À prouver
1. `unique_zero : ExisteUnique (fun n : Nat => n + n = 0)`
2. `egaux_si_unique : ExisteUnique p → p a → p b → a = b`

---
*Exercice* `Logique.Unique` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Logique.Unique` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Logique

/-- Il existe un et un seul `x` tel que `p x`. -/
def ExisteUnique {α : Type} (p : α → Prop) : Prop := ∃ x, p x ∧ ∀ y, p y → y = x

theorem unique_zero : ExisteUnique (fun n : Nat => n + n = 0) := by
  sorry

theorem egaux_si_unique {α : Type} {p : α → Prop} {a b : α} (h : ExisteUnique p) (ha : p a) (hb : p b) :
    a = b := by
  sorry

end Parcours.Logique

#verifier
