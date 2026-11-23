/- @parcours
titre: Chercher un mot dans un texte
difficulte: 3
requiert: Programmes.Recherche
indice: `commencePar_spec` : récurrence sur le motif, puis `cases t` ; `List.cons_prefix_cons`.
indice: Les deux autres : récurrence sur le texte en généralisant la position `i`, et `split at h` pour le `if`.
indice: `(b :: t).drop (k + 1) = t.drop k`.
-/
import Solutions.Programmes.Definitions

/-!
# Chercher un mot dans un texte

Le Ctrl+F de ton éditeur : chercher la première position où un motif apparaît dans un texte.
Version naïve : on essaie chaque position, et on regarde si le texte **commence par** le motif.

## À prouver
1. `commencePar_spec : commencePar m t = true ↔ m <+: t` (`<+:` : « est un préfixe de »)
2. `trouve_correct` : si on trouve la position `j`, le motif est bien là.
3. `absent_correct` : si on ne trouve rien, le motif n'apparaît nulle part.
4. `exemple_motif : chercherMotif [1, 2] [3, 1, 1, 2, 5] 0 = some 2`

## Ressources
- [Algorithme de recherche de sous-chaîne (Wikipédia)](https://fr.wikipedia.org/wiki/Algorithme_de_recherche_de_sous-cha%C3%AEne)
-/

namespace Parcours.Prog

def commencePar : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: m, b :: t => a == b && commencePar m t

/-- `chercherMotif m t i` : première position (comptée à partir de `i`) où `m` apparaît dans `t`. -/
def chercherMotif (m : List Nat) : List Nat → Nat → Option Nat
  | [], i => if m.isEmpty then some i else none
  | b :: t, i => if commencePar m (b :: t) then some i else chercherMotif m t (i + 1)

theorem commencePar_spec (m t : List Nat) : commencePar m t = true ↔ m <+: t := by -- @exo
  induction m generalizing t with
  | nil => simp [commencePar, List.nil_prefix]
  | cons a m ih =>
    cases t with
    | nil => simp [commencePar]
    | cons b t => simp [commencePar, ih, List.cons_prefix_cons]

theorem trouve_correct (m t : List Nat) (i j : Nat) (h : chercherMotif m t i = some j) :
    i ≤ j ∧ m <+: t.drop (j - i) := by -- @exo
  induction t generalizing i with
  | nil =>
    simp only [chercherMotif] at h
    split at h
    · rename_i hm
      cases h
      simp only [List.isEmpty_iff] at hm
      subst hm
      simp
    · simp at h
  | cons b t ih =>
    simp only [chercherMotif] at h
    split at h
    · rename_i hc
      cases h
      simpa using (commencePar_spec m (b :: t)).mp hc
    · obtain ⟨h1, h2⟩ := ih (i + 1) h
      refine ⟨by omega, ?_⟩
      rw [show j - i = (j - (i + 1)) + 1 by omega]
      simpa using h2

theorem absent_correct (m t : List Nat) (i : Nat) (h : chercherMotif m t i = none) :
    ∀ k, ¬ m <+: t.drop k := by -- @exo
  induction t generalizing i with
  | nil =>
    simp only [chercherMotif] at h
    split at h
    · simp at h
    · rename_i hm
      intro k hk
      simp only [List.drop_nil, List.prefix_nil] at hk
      subst hk
      simp at hm
  | cons b t ih =>
    simp only [chercherMotif] at h
    split at h
    · simp at h
    · rename_i hc
      intro k hk
      cases k with
      | zero => exact hc ((commencePar_spec m (b :: t)).mpr (by simpa using hk))
      | succ k => exact ih (i + 1) h k (by simpa using hk)

theorem exemple_motif : chercherMotif [1, 2] [3, 1, 1, 2, 5] 0 = some 2 := by -- @exo
  decide

end Parcours.Prog

#verifier
