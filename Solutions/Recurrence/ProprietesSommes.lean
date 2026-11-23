/- @parcours
titre: Manipuler des sommes
difficulte: 2
indice: Toutes les preuves sont des récurrences sur `n` avec `rw [somme_succ, somme_succ, …, ih]` puis `omega` ou `grind` (ou `Nat.mul_add`).
indice: `somme_decale` : récurrence sur `n` ; cas `succ` : `rw [somme_succ, ih, somme_succ]` puis `omega`.
indice: `somme_congr` : récurrence sur `n` ; l'hypothèse `h` doit être affaiblie pour `ih` : `ih (fun k hk => h k (by omega))`.
-/
import Solutions.Recurrence.Definitions

/-!
# Manipuler des sommes

Les règles de calcul sur `Σ` qu'on utilise sans y penser : linéarité, décalage d'indice,
termes égaux ⇒ sommes égales. Elles serviront pour le binôme de Newton.

## À prouver
1. `somme_add : somme (fun k => f k + g k) n = somme f n + somme g n`
2. `somme_mul : somme (fun k => c * f k) n = c * somme f n`
3. `somme_decale : somme f (n + 1) = f 0 + somme (fun k => f (k + 1)) n`
4. `somme_congr : (∀ k, k < n → f k = g k) → somme f n = somme g n`
5. `divise_somme : (∀ k, k < n → d ∣ f k) → d ∣ somme f n`
-/

namespace Parcours.Recurrence

theorem somme_add (f g : Nat → Nat) (n : Nat) :
    somme (fun k => f k + g k) n = somme f n + somme g n := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ, somme_succ, somme_succ, ih]
    omega

theorem somme_mul (c : Nat) (f : Nat → Nat) (n : Nat) :
    somme (fun k => c * f k) n = c * somme f n := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ, somme_succ, ih, Nat.mul_add]

theorem somme_decale (f : Nat → Nat) (n : Nat) :
    somme f (n + 1) = f 0 + somme (fun k => f (k + 1)) n := by -- @exo
  induction n with
  | zero => show 0 + f 0 = f 0 + 0; omega
  | succ n ih =>
    rw [somme_succ, ih, somme_succ]
    omega

theorem somme_congr {f g : Nat → Nat} {n : Nat} (h : ∀ k, k < n → f k = g k) :
    somme f n = somme g n := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ, somme_succ, ih (fun k hk => h k (by omega)), h n (by omega)]

theorem divise_somme {d : Nat} {f : Nat → Nat} {n : Nat} (h : ∀ k, k < n → d ∣ f k) :
    d ∣ somme f n := by -- @exo
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    rw [somme_succ]
    obtain ⟨a, ha⟩ := ih (fun k hk => h k (by omega))
    obtain ⟨b, hb⟩ := h n (by omega)
    exact ⟨a + b, by rw [ha, hb, Nat.mul_add]⟩

end Parcours.Recurrence

#verifier
