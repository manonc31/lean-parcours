/- @parcours
titre: Le langage IMP
difficulte: 3
indice: `determinisme` : récurrence sur la première exécution `h₁`, en généralisant `s₂` (`induction h₁ generalizing s₂ with`). Dans chaque cas, `cases h₂` puis utilise les hypothèses de récurrence.
indice: Pour les cas contradictoires (ex. : `b s = true` et `b s = false`), `simp_all` ou `rw` + `cases` concluent.
indice: `boucle_infinie` : on ne peut pas faire de récurrence directement (la commande n'est pas une variable). Astuce : `generalize hc : Com.tantque (fun _ => true) Com.skip = c at h`, puis `induction h` ; les cas impossibles se ferment avec `cases hc`.
-/
import Solutions.Informatique.Expressions

/-!
# Le langage IMP

Un petit langage impératif : affectation `x := a`, séquence `c₁ ; c₂`, `si b alors c₁ sinon c₂`,
`tant que b faire c`. Un **état** (`Store`) donne la valeur de chaque variable.

La **sémantique** est une relation inductive `Exec c s s'` : « exécuter `c` dans l'état `s` termine
dans l'état `s'` ». (Une relation et pas une fonction, car un programme peut ne pas terminer !)
Les expressions `a` et `b` sont directement des fonctions de l'état (pour simplifier).

## À prouver
1. `determinisme : Exec c s s₁ → Exec c s s₂ → s₁ = s₂`
2. `boucle_infinie : ¬Exec (tantque (fun _ => true) skip) s s'`

## Ressources
- [Sémantique opérationnelle (Wikipédia)](https://fr.wikipedia.org/wiki/S%C3%A9mantique_op%C3%A9rationnelle)
- [Software Foundations, volume 1, chapitre Imp](https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html) (en Coq, le cousin de Lean)
-/

namespace Parcours.Info

abbrev Store := Nat → Nat

def maj (s : Store) (x v : Nat) : Store := fun y => if y = x then v else s y

inductive Com where
  | skip
  | assign (x : Nat) (a : Store → Nat)
  | seq (c₁ c₂ : Com)
  | si (b : Store → Bool) (c₁ c₂ : Com)
  | tantque (b : Store → Bool) (c : Com)

open Com

inductive Exec : Com → Store → Store → Prop
  | skip (s : Store) : Exec skip s s
  | assign (s : Store) (x : Nat) (a : Store → Nat) : Exec (assign x a) s (maj s x (a s))
  | seq {c₁ c₂ : Com} {s s' s'' : Store} : Exec c₁ s s' → Exec c₂ s' s'' → Exec (seq c₁ c₂) s s''
  | si_vrai {b : Store → Bool} {c₁ c₂ : Com} {s s' : Store} :
      b s = true → Exec c₁ s s' → Exec (si b c₁ c₂) s s'
  | si_faux {b : Store → Bool} {c₁ c₂ : Com} {s s' : Store} :
      b s = false → Exec c₂ s s' → Exec (si b c₁ c₂) s s'
  | tq_faux {b : Store → Bool} {c : Com} {s : Store} : b s = false → Exec (tantque b c) s s
  | tq_vrai {b : Store → Bool} {c : Com} {s s' s'' : Store} :
      b s = true → Exec c s s' → Exec (tantque b c) s' s'' → Exec (tantque b c) s s''

theorem determinisme {c : Com} {s s₁ s₂ : Store} (h₁ : Exec c s s₁) (h₂ : Exec c s s₂) : s₁ = s₂ := by -- @exo
  induction h₁ generalizing s₂ with
  | skip => cases h₂; rfl
  | assign => cases h₂; rfl
  | seq _ _ ih₁ ih₂ =>
    cases h₂ with
    | seq h₂₁ h₂₂ =>
      rw [← ih₁ h₂₁] at h₂₂
      exact ih₂ h₂₂
  | si_vrai hb _ ih =>
    cases h₂ with
    | si_vrai _ h => exact ih h
    | si_faux hb' _ => simp_all
  | si_faux hb _ ih =>
    cases h₂ with
    | si_vrai hb' _ => simp_all
    | si_faux _ h => exact ih h
  | tq_faux hb =>
    cases h₂ with
    | tq_faux _ => rfl
    | tq_vrai hb' _ _ => simp_all
  | tq_vrai hb _ _ ih₁ ih₂ =>
    cases h₂ with
    | tq_faux hb' => simp_all
    | tq_vrai _ h₂₁ h₂₂ =>
      rw [← ih₁ h₂₁] at h₂₂
      exact ih₂ h₂₂

theorem boucle_infinie (s s' : Store) : ¬Exec (tantque (fun _ => true) skip) s s' := by -- @exo
  intro h
  generalize hc : tantque (fun _ => true) skip = c at h
  induction h with
  | tq_faux hb =>
    cases hc
    simp at hb
  | tq_vrai _ _ _ _ ih₂ => exact ih₂ hc
  | _ => cases hc

end Parcours.Info

#verifier
