/- @parcours
titre: La fonction 91 de McCarthy
difficulte: 4
indice: Lemme de monotonie : si le calcul réussit avec `f` unités de carburant, il réussit (avec le même résultat) avec plus de carburant. Récurrence sur `f` en généralisant `n` et `v`. `mc91_succ` déplie un cran, `ite_eq_left`/`ite_eq_right` simplifient le `if`, `Option.bind_eq_some_iff` décompose le `bind`.
indice: Théorème principal : écris-le comme une fonction récursive avec `termination_by 101 - n` (c'est une récurrence « vers le haut » !).
indice: Si `90 ≤ n ≤ 100` : `mc91 (n + 11)` vaut `n + 1` (une seule étape), puis on recommence avec `n + 1` (plus proche de 101). Si `n < 90` : `mc91 (n + 11) = 91` puis `mc91 91 = 91`, deux appels « récursifs ».
-/
import Solutions.Recurrence.Definitions

/-!
# La fonction 91 de McCarthy

```
M(n) = n - 10           si n > 100
M(n) = M(M(n + 11))     sinon
```

Une récursion **imbriquée** : l'argument de l'appel extérieur est lui-même un appel récursif !
Surprise : pour tout `n ≤ 100`, `M(n) = 91`. Prouver que ça termine est délicat (ce n'est pas l'argument
qui diminue). On contourne avec du **carburant** : `mc91 f n` fait au plus `f` étapes et rend
`none` s'il manque de carburant. On prouve qu'avec assez de carburant, le résultat est `91`.

## À prouver
1. `mc91_mono : mc91 f n = some v → mc91 (f + k) n = some v`
2. `mc91_spec : n ≤ 100 → ∃ f, mc91 f n = some 91`

## Ressources
- [Fonction 91 de McCarthy (Wikipédia)](https://fr.wikipedia.org/wiki/Fonction_91_de_McCarthy)
-/

namespace Parcours.Term

def mc91 : Nat → Nat → Option Nat
  | 0, _ => none
  | f + 1, n => if n > 100 then some (n - 10) else (mc91 f (n + 11)).bind (mc91 f)

theorem mc91_succ (f n : Nat) :
    mc91 (f + 1) n = if n > 100 then some (n - 10) else (mc91 f (n + 11)).bind (mc91 f) := rfl

theorem mc91_mono (f k n v : Nat) (h : mc91 f n = some v) : mc91 (f + k) n = some v := by -- @exo
  induction f generalizing n v with
  | zero => simp [mc91] at h
  | succ f ih =>
    rw [show f + 1 + k = (f + k) + 1 by omega, mc91_succ]
    rw [mc91_succ] at h
    by_cases hn : n > 100
    · rw [ite_eq_left hn] at h ⊢
      exact h
    · rw [ite_eq_right hn] at h ⊢
      obtain ⟨w, hw1, hw2⟩ := Option.bind_eq_some_iff.mp h
      rw [ih _ _ hw1, Option.bind_some]
      exact ih _ _ hw2

theorem mc91_spec (n : Nat) (hn : n ≤ 100) : ∃ f, mc91 f n = some 91 := by -- @exo
  by_cases h90 : 90 ≤ n
  · by_cases h100 : n = 100
    · subst h100
      exact ⟨2, rfl⟩
    · obtain ⟨f, hf⟩ := mc91_spec (n + 1) (by omega)
      have h1 : mc91 (f + 1) (n + 11) = some (n + 1) := by
        rw [mc91_succ, ite_eq_left (by omega)]
        congr 1
      refine ⟨f + 1 + 1, ?_⟩
      rw [mc91_succ, ite_eq_right (by omega), h1, Option.bind_some]
      exact mc91_mono f 1 _ _ hf
  · obtain ⟨f₁, h₁⟩ := mc91_spec (n + 11) (by omega)
    obtain ⟨f₂, h₂⟩ := mc91_spec 91 (by omega)
    refine ⟨f₁ + f₂ + 1, ?_⟩
    rw [mc91_succ, ite_eq_right (by omega), mc91_mono f₁ f₂ _ _ h₁, Option.bind_some,
      Nat.add_comm f₁ f₂]
    exact mc91_mono f₂ f₁ _ _ h₂
termination_by 101 - n

end Parcours.Term

#verifier
