/- @parcours
titre: Existe-t-il un nombre parfait impair ?
difficulte: 5
genre: ouvert
requiert: Arithmetique.InfinitePremiers
indice: Personne au monde ne sait le prouver. Si tu y arrives, publie-le (et préviens-moi) !
indice: Ce que tu PEUX faire : vérifier l'énoncé pour les petites valeurs, avec `decide` ou `#eval`. Essaie !
-/
import Solutions.Arithmetique.Definitions

/-!
# ♾️ Existe-t-il un nombre parfait impair ?

Un nombre est **parfait** s'il est égal à la somme de ses diviseurs stricts (6 = 1 + 2 + 3, 28 = 1 + 2 + 4 + 7 + 14). Tous les nombres parfaits connus sont pairs. Existe-t-il un nombre parfait **impair** ? On sait qu'il devrait dépasser 10¹⁵⁰⁰. Le plus vieux problème ouvert des mathématiques (Nicomaque, vers l'an 100).

**C'est un problème ouvert** : personne ne connaît de preuve (ni de contre-exemple). Il est là pour
le panache, et pour te montrer qu'en quelques lignes de Lean on peut énoncer des questions que
l'humanité ne sait pas résoudre.

## Ressources
- [Nombre parfait (Wikipédia)](https://fr.wikipedia.org/wiki/Nombre_parfait)
-/

namespace Parcours.Ouverts

/-- La somme de tous les diviseurs de `n` (y compris `n`). -/
def sommeDiviseurs (n : Nat) : Nat :=
  ((List.range (n + 1)).filter (fun d => d != 0 && n % d == 0)).sum

example : sommeDiviseurs 28 = 56 := by decide

theorem pas_de_parfait_impair : ¬∃ n, n % 2 = 1 ∧ sommeDiviseurs n = 2 * n := by -- @exo
  sorry

end Parcours.Ouverts

#verifier
