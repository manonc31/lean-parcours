/- @parcours
titre: Le jeu du plus ou moins
difficulte: 2
requiert: Programmes.Recherche
indice: Fais d'abord vérifier à `decide +kernel` un énoncé booléen sur les 100 secrets (avec `Option.getD` et `Option.isSome`).
indice: Puis `cases e : essais s 10 0 100` pour récupérer le nombre d'essais.
-/
import Solutions.Programmes.Definitions

/-!
# Le jeu du plus ou moins

« Je pense à un nombre entre 0 et 99. » À chaque essai, on te répond « plus grand » ou « plus
petit ». En visant toujours le **milieu** de l'intervalle restant (dichotomie), **7 essais**
suffisent toujours, car `2^7 = 128 ≥ 100`.

## À prouver
1. `sept_essais` : pour chaque nombre secret, la stratégie le trouve en au plus 7 essais.
2. `parfois_sept` : et il existe un secret qui en demande vraiment 7 (par exemple 0).

## Ressources
- [Recherche dichotomique (Wikipédia)](https://fr.wikipedia.org/wiki/Recherche_dichotomique)
-/

namespace Parcours.Prog

/-- Nombre d'essais pour trouver `s` dans `[lo, hi)` en visant le milieu (`none` si échec). -/
def essais (s : Nat) : Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | f + 1, lo, hi =>
    let m := (lo + hi) / 2
    if s = m then some 1
    else if s < m then (essais s f lo m).map (· + 1)
    else (essais s f (m + 1) hi).map (· + 1)

theorem sept_essais : ∀ s, s < 100 → ∃ k, essais s 10 0 100 = some k ∧ k ≤ 7 := by -- @exo
  intro s hs
  have : ∀ s, s < 100 → ((essais s 10 0 100).getD 100) ≤ 7 ∧ (essais s 10 0 100).isSome := by
    decide +kernel
  obtain ⟨h1, h2⟩ := this s hs
  cases e : essais s 10 0 100 with
  | none => simp [e] at h2
  | some k => exact ⟨k, rfl, by simpa [e] using h1⟩

theorem parfois_sept : essais 0 10 0 100 = some 7 := by -- @exo
  decide

end Parcours.Prog

#verifier
