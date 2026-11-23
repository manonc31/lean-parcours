import Exercices.Arithmetique.Definitions

/-!
# ♾️ Existe-t-il un nombre parfait impair ?

Un nombre est **parfait** s'il est égal à la somme de ses diviseurs stricts (6 = 1 + 2 + 3, 28 = 1 + 2 + 4 + 7 + 14). Tous les nombres parfaits connus sont pairs. Existe-t-il un nombre parfait **impair** ? On sait qu'il devrait dépasser 10¹⁵⁰⁰. Le plus vieux problème ouvert des mathématiques (Nicomaque, vers l'an 100).

**C'est un problème ouvert** : personne ne connaît de preuve (ni de contre-exemple). Il est là pour
le panache, et pour te montrer qu'en quelques lignes de Lean on peut énoncer des questions que
l'humanité ne sait pas résoudre.

## Ressources
- [Nombre parfait (Wikipédia)](https://fr.wikipedia.org/wiki/Nombre_parfait)

---
*Exercice* `Ouverts.ParfaitImpair` · difficulté ★★★★★

💡 Indices : `./parcours indice Ouverts.ParfaitImpair` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Ouverts

/-- La somme de tous les diviseurs de `n` (y compris `n`). -/
def sommeDiviseurs (n : Nat) : Nat :=
  ((List.range (n + 1)).filter (fun d => d != 0 && n % d == 0)).sum

example : sommeDiviseurs 28 = 56 := by decide

theorem pas_de_parfait_impair : ¬∃ n, n % 2 = 1 ∧ sommeDiviseurs n = 2 * n := by
  sorry

end Parcours.Ouverts

#verifier
