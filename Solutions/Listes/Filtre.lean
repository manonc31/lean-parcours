/- @parcours
titre: Filtrer
difficulte: 2
indice: `filtre_concat` : récurrence sur `l₁`. Dans le cas `cons x l`, raisonne par cas sur `p x` : `cases h : p x`, puis `simp only [filtre, h]`.
indice: `longueur_filtre` : récurrence ; dans le cas `cons`, `show longueur (if p x then x ∷ filtre p l else filtre p l) ≤ longueur l + 1`, puis `cases p x`, et dans chaque cas un `show` qui simplifie le `if`, puis `omega`.
-/
import Solutions.Listes.Longueur

/-!
# Filtrer

`filtre p l` garde les éléments `x` de `l` tels que `p x = true`.

## À prouver
1. `filtre_concat : filtre p (l₁ ++ l₂) = filtre p l₁ ++ filtre p l₂`
2. `longueur_filtre : longueur (filtre p l) ≤ longueur l`
-/

namespace Parcours.Listes.Liste

variable {α : Type}

theorem filtre_concat (p : α → Bool) (l₁ l₂ : Liste α) :
    filtre p (l₁ ++ l₂) = filtre p l₁ ++ filtre p l₂ := by -- @exo
  induction l₁ with
  | nil => rfl
  | cons x l ih =>
    rw [cons_concat]
    cases h : p x
    · simp only [filtre, h, ih]
      rfl
    · simp only [filtre, h, ih]
      rfl

theorem longueur_filtre (p : α → Bool) (l : Liste α) : longueur (filtre p l) ≤ longueur l := by -- @exo
  induction l with
  | nil => exact Nat.le_refl 0
  | cons x l ih =>
    show longueur (if p x then x ∷ filtre p l else filtre p l) ≤ longueur l + 1
    cases p x
    · show longueur (filtre p l) ≤ longueur l + 1
      omega
    · show longueur (filtre p l) + 1 ≤ longueur l + 1
      omega

end Parcours.Listes.Liste

#verifier
