/- @parcours
celebre: 63
titre: Le théorème de Cantor
difficulte: 3
requiert: Logique.Barbier
indice: Suppose `h` et considère la « propriété diagonale » `g := fun x => ¬f x x`. Par `h`, il existe `a` avec `f a = g`.
indice: `congrFun ha a : f a a = ¬f a a` (évaluer l'égalité de fonctions en `a`). Ou bien `rw` sur `ha`…
indice: Avec `h1 : f a a = ¬f a a`, `Eq.mp h1 : f a a → ¬f a a` et `Eq.mpr h1 : ¬f a a → f a a`. C'est le barbier !
-/
import ParcoursOutils

/-!
# Le théorème de Cantor

> Il n'y a pas de surjection d'un ensemble vers l'ensemble de ses parties.

Ici, une « partie » de `α` est une propriété `α → Prop`. Le théorème dit : quelle que soit
la façon `f` d'associer à chaque élément `a` une propriété `f a`, il existe une propriété `g`
qui n'est **aucune** des `f a`. Conséquence : il y a « plus » de parties de ℕ que d'entiers.
C'est l'**argument diagonal** de Cantor (1891).

## À prouver
`cantor (f : α → (α → Prop)) : ¬∀ g : α → Prop, ∃ a, f a = g`

## Ressources
- [Théorème de Cantor (Wikipédia)](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_de_Cantor)
- [Argument de la diagonale de Cantor (Wikipédia)](https://fr.wikipedia.org/wiki/Argument_de_la_diagonale_de_Cantor)
-/

namespace Parcours.Logique

theorem cantor {α : Type} (f : α → (α → Prop)) : ¬∀ g : α → Prop, ∃ a, f a = g := by -- @exo
  intro h
  obtain ⟨a, ha⟩ := h (fun x => ¬f x x)
  have h1 : f a a = ¬f a a := congrFun ha a
  have hn : ¬f a a := fun hfa => (Eq.mp h1 hfa) hfa
  exact hn (Eq.mpr h1 hn)

end Parcours.Logique

#verifier
