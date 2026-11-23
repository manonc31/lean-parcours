/- @parcours
titre: L'hôtel de Hilbert
difficulte: 4
indice: `tri_ge` : récurrence. `code_suivant` : par cas sur `a` (`obtain ⟨a, b⟩ := p` puis `cases a`) ; `simp [suivant, code, tri]` puis `omega` (écris `a + 1 + b = a + (b + 1)` si besoin).
indice: `code_decode` : récurrence sur `n`, avec `code_suivant`.
indice: `decode_code` : prouve `∀ n, ∀ p, code p = n → decode n = p` par récurrence sur `n`. Tout couple `≠ (0,0)` est le `suivant` d'un autre : `(a, b+1) = suivant (a+1, b)` et `(a+1, 0) = suivant (0, a)`.
indice: Cas `n = 0` : `code (a, b) = 0` force `b = 0` et `tri (a + b) = 0`, donc `a + b = 0` (car `a + b ≤ tri (a + b)`).
-/
import Solutions.Combinatoire.Definitions

/-!
# L'hôtel de Hilbert

Un hôtel a une infinité de chambres numérotées `0, 1, 2, …`, toutes occupées. Arrive un car
infini de cars infinis de touristes : le touriste `b` du car `a`. Peut-on loger tout le monde ?
Oui ! Il y a autant de couples `(a, b)` que d'entiers : on les énumère **par diagonales**.

```
(0,0) → (1,0) → (0,1) → (2,0) → (1,1) → (0,2) → (3,0) → …
  0       1       2       3       4       5       6
```

`code (a, b) = tri (a + b) + b` (avec `tri m = 0 + 1 + ⋯ + m`) et `decode` parcourt les diagonales.

## À prouver
1. `tri_ge : m ≤ tri m`
2. `code_suivant : code (suivant p) = code p + 1`
3. `code_decode : code (decode n) = n`
4. `decode_code : decode (code p) = p`
5. `hilbert : ∃ f : Nat × Nat → Nat, (∀ p q, f p = f q → p = q) ∧ ∀ n, ∃ p, f p = n`

## Ressources
- [Hôtel de Hilbert (Wikipédia)](https://fr.wikipedia.org/wiki/H%C3%B4tel_de_Hilbert)
- [Fonction de couplage (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Pairing_function)
-/

namespace Parcours.Combi

def tri : Nat → Nat
  | 0 => 0
  | m + 1 => tri m + m + 1

def code (p : Nat × Nat) : Nat := tri (p.1 + p.2) + p.2

def suivant : Nat × Nat → Nat × Nat
  | (0, b) => (b + 1, 0)
  | (a + 1, b) => (a, b + 1)

def decode : Nat → Nat × Nat
  | 0 => (0, 0)
  | n + 1 => suivant (decode n)

theorem tri_ge (m : Nat) : m ≤ tri m := by -- @exo
  induction m with
  | zero => exact Nat.le_refl 0
  | succ m ih =>
    show m + 1 ≤ tri m + m + 1
    omega

theorem code_suivant (p : Nat × Nat) : code (suivant p) = code p + 1 := by -- @exo
  obtain ⟨a, b⟩ := p
  cases a with
  | zero =>
    simp only [suivant, code, tri, Nat.zero_add, Nat.add_zero]
  | succ a =>
    simp only [suivant, code]
    rw [show a + 1 + b = a + (b + 1) by omega]
    omega

theorem code_decode (n : Nat) : code (decode n) = n := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih => rw [decode, code_suivant, ih]

theorem decode_code (p : Nat × Nat) : decode (code p) = p := by -- @exo
  have h : ∀ n, ∀ p : Nat × Nat, code p = n → decode n = p := by
    intro n
    induction n with
    | zero =>
      intro ⟨a, b⟩ hp
      simp only [code] at hp
      have := tri_ge (a + b)
      have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      rw [ha, hb]
      rfl
    | succ n ih =>
      intro ⟨a, b⟩ hp
      cases b with
      | succ b =>
        have hq : code (a + 1, b) = n := by
          have := code_suivant (a + 1, b)
          simp only [suivant] at this
          omega
        show suivant (decode n) = (a, b + 1)
        rw [ih _ hq]
        rfl
      | zero =>
        cases a with
        | zero => simp [code, tri] at hp
        | succ a =>
          have hq : code (0, a) = n := by
            have := code_suivant (0, a)
            simp only [suivant] at this
            omega
          show suivant (decode n) = (a + 1, 0)
          rw [ih _ hq]
          rfl
  exact h _ p rfl

theorem hilbert : ∃ f : Nat × Nat → Nat, (∀ p q, f p = f q → p = q) ∧ ∀ n, ∃ p, f p = n := by -- @exo
  refine ⟨code, ?_, ?_⟩
  · intro p q h
    rw [← decode_code p, ← decode_code q, h]
  · intro n
    exact ⟨decode n, code_decode n⟩

end Parcours.Combi

#verifier
