/- @parcours
titre: Le principe du bon ordre
difficulte: 4
indice: Par l'absurde : suppose qu'aucun `m` n'est un minimum (`apply Classical.byContradiction; intro hmin`).
indice: Montre alors `∀ n, ¬P n` par récurrence forte : si `P n`, alors `n` serait un minimum, car tout `k` avec `P k` vérifie `n ≤ k` (sinon `k < n`, et par hypothèse de récurrence `¬P k`).
indice: Pour « sinon `k < n` » : `le_total n k` donne `n ≤ k` ou `k ≤ n` ; dans le second cas, si `k ≠ n` alors `k < n` (`lt_iff_le_ne`).
-/
import Solutions.Naturels.RecurrenceForte
import Solutions.Naturels.LeTotal

/-!
# Le principe du bon ordre

> Toute partie non vide de ℕ a un plus petit élément.

C'est équivalent à la récurrence (forte). Faux dans ℤ (pas de plus petit entier relatif),
faux dans les rationnels positifs (pas de plus petit rationnel > 0).

## À prouver
`bon_ordre (P : ℕ → Prop) (h : ∃ n, P n) : ∃ m, P m ∧ ∀ k, P k → m ≤ k`

## Ressources
- [Bon ordre (Wikipédia)](https://fr.wikipedia.org/wiki/Bon_ordre)
-/

namespace Parcours.ℕ

theorem bon_ordre (P : ℕ → Prop) (h : ∃ n, P n) : ∃ m, P m ∧ ∀ k, P k → m ≤ k := by -- @exo
  apply Classical.byContradiction
  intro hmin
  have hnon : ∀ n, ¬P n := by
    intro n
    apply recurrence_forte (fun n => ¬P n)
    intro n ih hpn
    apply hmin
    refine ⟨n, hpn, ?_⟩
    intro k hk
    rcases le_total n k with hnk | hkn
    · exact hnk
    · rcases Classical.em (k = n) with he | hne
      · rw [he]
        exact le_refl n
      · exact absurd hk (ih k ((lt_iff_le_ne k n).mpr ⟨hkn, hne⟩))
  obtain ⟨n, hn⟩ := h
  exact hnon n hn

end Parcours.ℕ

#verifier
