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

---
*Exercice* `Logique.Cantor` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Logique.Cantor` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Logique

theorem cantor {α : Type} (f : α → (α → Prop)) : ¬∀ g : α → Prop, ∃ a, f a = g := by
  sorry

end Parcours.Logique

#verifier
