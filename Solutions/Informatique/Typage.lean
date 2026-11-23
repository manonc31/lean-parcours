/- @parcours
titre: Les programmes bien typés ne plantent pas
difficulte: 4
requiert: Informatique.Expressions
indice: Récurrence sur la dérivation de typage (`induction h with`).
indice: Pour `plus` : les hypothèses de récurrence donnent deux valeurs de type `nat`. Fais `cases` sur ces valeurs : le cas booléen est impossible (`False.elim t₁`, car `Val.aType (.b _) .nat` est `False`).
indice: Pour calculer `eval` : `simp [Exp.eval, h₁, h₂]`.
-/
import Solutions.Informatique.Expressions

/-!
# Les programmes bien typés ne plantent pas

Un petit langage avec des entiers, des booléens, `+`, `si … alors … sinon` et `=`. Certaines expressions
n'ont pas de sens (`vrai + 3`) : l'évaluation échoue (`none`). Un **système de types** les rejette
avant l'exécution. Le théorème de **sûreté** : une expression bien typée s'évalue toujours, et donne
une valeur du bon type.

Robin Milner (1978) : *« Well-typed programs cannot go wrong. »* C'est la promesse des langages typés
(OCaml, Haskell, Rust… et Lean).

## À prouver
`surete : ATy e t → ∃ v, eval e = some v ∧ v.aType t`

## Ressources
- [Sûreté du typage (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Type_safety)
-/

namespace Parcours.Info

inductive Ty where
  | nat
  | bool

inductive Exp where
  | num (k : Nat)
  | vrai
  | faux
  | plus (e₁ e₂ : Exp)
  | si (c e₁ e₂ : Exp)
  | egal (e₁ e₂ : Exp)

inductive Val where
  | n (k : Nat)
  | b (v : Bool)

def Exp.eval : Exp → Option Val
  | .num k => some (.n k)
  | .vrai => some (.b true)
  | .faux => some (.b false)
  | .plus e₁ e₂ =>
    match e₁.eval, e₂.eval with
    | some (.n a), some (.n b) => some (.n (a + b))
    | _, _ => none
  | .si c e₁ e₂ =>
    match c.eval with
    | some (.b true) => e₁.eval
    | some (.b false) => e₂.eval
    | _ => none
  | .egal e₁ e₂ =>
    match e₁.eval, e₂.eval with
    | some (.n a), some (.n b) => some (.b (a == b))
    | _, _ => none

/-- `ATy e t` : l'expression `e` a le type `t`. -/
inductive ATy : Exp → Ty → Prop
  | num (k : Nat) : ATy (.num k) .nat
  | vrai : ATy .vrai .bool
  | faux : ATy .faux .bool
  | plus {e₁ e₂ : Exp} : ATy e₁ .nat → ATy e₂ .nat → ATy (.plus e₁ e₂) .nat
  | si {c e₁ e₂ : Exp} {t : Ty} : ATy c .bool → ATy e₁ t → ATy e₂ t → ATy (.si c e₁ e₂) t
  | egal {e₁ e₂ : Exp} : ATy e₁ .nat → ATy e₂ .nat → ATy (.egal e₁ e₂) .bool

/-- Une valeur a-t-elle un type donné ? -/
def Val.aType : Val → Ty → Prop
  | .n _, .nat => True
  | .b _, .bool => True
  | _, _ => False

theorem surete {e : Exp} {t : Ty} (h : ATy e t) : ∃ v, e.eval = some v ∧ v.aType t := by -- @exo
  induction h with
  | num k => exact ⟨.n k, rfl, trivial⟩
  | vrai => exact ⟨.b true, rfl, trivial⟩
  | faux => exact ⟨.b false, rfl, trivial⟩
  | plus _ _ ih₁ ih₂ =>
    obtain ⟨v₁, h₁, t₁⟩ := ih₁
    obtain ⟨v₂, h₂, t₂⟩ := ih₂
    cases v₁ with
    | b _ => exact False.elim t₁
    | n a =>
      cases v₂ with
      | b _ => exact False.elim t₂
      | n b => exact ⟨.n (a + b), by simp [Exp.eval, h₁, h₂], trivial⟩
  | si _ _ _ ihc ih₁ ih₂ =>
    obtain ⟨vc, hc, tc⟩ := ihc
    cases vc with
    | n _ => exact False.elim tc
    | b bv =>
      cases bv
      · obtain ⟨v, hv, tv⟩ := ih₂
        exact ⟨v, by simp [Exp.eval, hc, hv], tv⟩
      · obtain ⟨v, hv, tv⟩ := ih₁
        exact ⟨v, by simp [Exp.eval, hc, hv], tv⟩
  | egal _ _ ih₁ ih₂ =>
    obtain ⟨v₁, h₁, t₁⟩ := ih₁
    obtain ⟨v₂, h₂, t₂⟩ := ih₂
    cases v₁ with
    | b _ => exact False.elim t₁
    | n a =>
      cases v₂ with
      | b _ => exact False.elim t₂
      | n b => exact ⟨.b (a == b), by simp [Exp.eval, h₁, h₂], trivial⟩

end Parcours.Info

#verifier
