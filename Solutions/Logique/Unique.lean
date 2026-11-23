/- @parcours
titre: Existence et unicité
difficulte: 2
requiert: Logique.Existe
indice: `ExisteUnique p` signifie `∃ x, p x ∧ ∀ y, p y → y = x`. Pour le prouver : `refine ⟨témoin, preuve, ?_⟩`.
indice: `unique_zero` : témoin `0` ; pour l'unicité, `intro y hy`, et `hy : y + y = 0` donne `y = 0` (`omega`, débloqué ici car l'exercice dépend du pont des entiers… sinon raisonne par cas sur `y`).
indice: `egaux_si_unique` : décompose `obtain ⟨x, hx, hu⟩ := h`, puis `hu a ha` et `hu b hb`.
-/
import Solutions.Logique.Bilan
import Solutions.Naturels.Transfert

/-!
# Existence et unicité

« Il existe **un et un seul** `x` tel que `p x` » : on le définit comme
`ExisteUnique p := ∃ x, p x ∧ ∀ y, p y → y = x` (Mathlib le note `∃! x, p x`).

## À prouver
1. `unique_zero : ExisteUnique (fun n : Nat => n + n = 0)`
2. `egaux_si_unique : ExisteUnique p → p a → p b → a = b`
-/

namespace Parcours.Logique

/-- Il existe un et un seul `x` tel que `p x`. -/
def ExisteUnique {α : Type} (p : α → Prop) : Prop := ∃ x, p x ∧ ∀ y, p y → y = x

theorem unique_zero : ExisteUnique (fun n : Nat => n + n = 0) := by -- @exo
  refine ⟨0, rfl, ?_⟩
  intro y hy
  omega

theorem egaux_si_unique {α : Type} {p : α → Prop} {a b : α} (h : ExisteUnique p) (ha : p a) (hb : p b) :
    a = b := by -- @exo
  obtain ⟨x, _, hu⟩ := h
  rw [hu a ha, hu b hb]

end Parcours.Logique

#verifier
