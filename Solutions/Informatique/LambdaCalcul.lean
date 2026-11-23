/- @parcours
titre: Le λ-calcul et la boucle Ω
difficulte: 3
indice: `omega_boucle` : c'est exactement la règle `Reduit.beta`. Le résultat de la substitution se calcule : `exact Reduit.beta _ _` (Lean vérifie par calcul que `substituer 0 δ (app (var 0) (var 0)) = Ω`).
indice: `etoile_trans` : récurrence sur la première réduction `h₁`.
indice: `identite_app` : `I t` se réduit en une étape vers `substituer 0 t (var 0) = t`.
-/
import Solutions.Informatique.Expressions

/-!
# Le λ-calcul et la boucle Ω

Le **λ-calcul** (Church, 1936) est le plus petit langage de programmation : des variables, des
fonctions `λx. t` et des applications `t u`. Le calcul est une seule règle, la **β-réduction** :
`(λx. t) u  →  t[x := u]`. Il est aussi puissant que les machines de Turing.

On code les variables par des **indices de de Bruijn** : `var 0` désigne la variable liée par le
`λ` le plus proche, `var 1` le suivant, etc. (plus de problème de renommage !).

`Ω = (λx. x x) (λx. x x)` se réduit… en lui-même : un programme qui boucle à l'infini.

## À prouver
1. `omega_boucle : Reduit Ω Ω`
2. `etoile_trans` : la réduction en plusieurs étapes est transitive.
3. `identite_app : Reduit (app I t) t` où `I = λx. x`.

## Ressources
- [Lambda-calcul (Wikipédia)](https://fr.wikipedia.org/wiki/Lambda-calcul)
- [Indices de De Bruijn (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/De_Bruijn_index)
-/

namespace Parcours.Info

inductive Terme where
  | var (n : Nat)
  | app (t u : Terme)
  | lam (t : Terme)

open Terme

/-- Décale de 1 les variables libres d'indice `≥ c`. -/
def relever (c : Nat) : Terme → Terme
  | var k => if k < c then var k else var (k + 1)
  | app t u => app (relever c t) (relever c u)
  | lam t => lam (relever (c + 1) t)

/-- Remplace la variable `j` par `s` (et décrémente les variables libres au-dessus de `j`). -/
def substituer (j : Nat) (s : Terme) : Terme → Terme
  | var k => if k < j then var k else if k = j then s else var (k - 1)
  | app t u => app (substituer j s t) (substituer j s u)
  | lam t => lam (substituer (j + 1) (relever 0 s) t)

/-- Une étape de β-réduction (n'importe où dans le terme). -/
inductive Reduit : Terme → Terme → Prop
  | beta (t s : Terme) : Reduit (app (lam t) s) (substituer 0 s t)
  | app_g {t t' : Terme} (u : Terme) : Reduit t t' → Reduit (app t u) (app t' u)
  | app_d (t : Terme) {u u' : Terme} : Reduit u u' → Reduit (app t u) (app t u')
  | lam {t t' : Terme} : Reduit t t' → Reduit (lam t) (lam t')

/-- Zéro, une ou plusieurs étapes. -/
inductive ReduitEtoile : Terme → Terme → Prop
  | refl (t : Terme) : ReduitEtoile t t
  | etape {t u v : Terme} : Reduit t u → ReduitEtoile u v → ReduitEtoile t v

def δ : Terme := lam (app (var 0) (var 0))
def Ω : Terme := app δ δ
def I : Terme := lam (var 0)

theorem omega_boucle : Reduit Ω Ω := by -- @exo
  exact Reduit.beta _ _

theorem etoile_trans {t u v : Terme} (h₁ : ReduitEtoile t u) (h₂ : ReduitEtoile u v) :
    ReduitEtoile t v := by -- @exo
  induction h₁ with
  | refl => exact h₂
  | etape r _ ih => exact ReduitEtoile.etape r (ih h₂)

theorem identite_app (t : Terme) : Reduit (app I t) t := by -- @exo
  exact Reduit.beta _ _

end Parcours.Info

#verifier
