import Exercices.Informatique.Expressions

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

---
*Exercice* `Informatique.LogiqueProp` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Informatique.LogiqueProp` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
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

theorem correction {f : Formule} (h : Prouvable f) (v : Nat → Bool) : f.eval v = true := by
  sorry

theorem identite (a : Formule) : Prouvable (imp a a) := by
  sorry

end Parcours.Info

#verifier
