/- @parcours
titre: Un système de preuve correct
difficulte: 3
indice: `correction` : récurrence sur la preuve `h` (`induction h with`). Pour chaque axiome, déplie `eval` et examine les valeurs booléennes : `simp only [eval]`, puis `cases eval v a <;> cases eval v b <;> rfl`.
indice: Cas `mp` : `ih₁ : eval v (imp a b) = true` et `ih₂ : eval v a = true` ; déplie `eval` dans `ih₁`, réécris avec `ih₂`.
indice: `identite` : c'est la célèbre preuve `I = S K K`. Utilise `mp` deux fois avec `s a (imp a a) a`, `k a (imp a a)` et `k a a`.
-/
import Solutions.Informatique.Expressions

/-!
# Un système de preuve correct

On définit des **formules** (variables, faux, implication), leur **valeur de vérité** sous une
valuation `v : Nat → Bool`, et un **système de preuve à la Hilbert** : trois axiomes et le modus ponens.

On fait ici des mathématiques **sur** la logique (de la métamathématique) : prouver, en Lean,
des propriétés d'un autre système de preuve.

## À prouver
1. `correction` : tout ce qui est prouvable est vrai pour toute valuation (une **tautologie**).
2. `identite` : `a → a` est prouvable (et la preuve n'est pas si évidente !).

## Ressources
- [Système à la Hilbert (Wikipédia)](https://fr.wikipedia.org/wiki/Syst%C3%A8me_%C3%A0_la_Hilbert)
- [Combinatoire SKI (Wikipédia)](https://fr.wikipedia.org/wiki/Logique_combinatoire)
-/

namespace Parcours.Info

inductive Formule where
  | var (i : Nat)
  | faux
  | imp (a b : Formule)

open Formule

def Formule.eval (v : Nat → Bool) : Formule → Bool
  | var i => v i
  | faux => false
  | imp a b => !a.eval v || b.eval v

inductive Prouvable : Formule → Prop
  | k (a b : Formule) : Prouvable (imp a (imp b a))
  | s (a b c : Formule) : Prouvable (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))
  | dn (a : Formule) : Prouvable (imp (imp (imp a faux) faux) a)
  | mp {a b : Formule} : Prouvable (imp a b) → Prouvable a → Prouvable b

theorem correction {f : Formule} (h : Prouvable f) (v : Nat → Bool) : f.eval v = true := by -- @exo
  induction h with
  | k a b =>
    simp only [Formule.eval]
    cases a.eval v <;> cases b.eval v <;> rfl
  | s a b c =>
    simp only [Formule.eval]
    cases a.eval v <;> cases b.eval v <;> cases c.eval v <;> rfl
  | dn a =>
    simp only [Formule.eval]
    cases a.eval v <;> rfl
  | mp _ _ ih₁ ih₂ =>
    simp only [Formule.eval, ih₂] at ih₁
    simpa using ih₁

theorem identite (a : Formule) : Prouvable (imp a a) := by -- @exo
  exact Prouvable.mp (Prouvable.mp (Prouvable.s a (imp a a) a) (Prouvable.k a (imp a a))) (Prouvable.k a a)

end Parcours.Info

#verifier
