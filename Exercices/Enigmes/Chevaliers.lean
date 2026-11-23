import Exercices.Logique.Bilan

/-!
# Chevaliers et menteurs

Sur l'île de Raymond Smullyan, les **chevaliers** disent toujours la vérité, les **menteurs**
mentent toujours. On code « chevalier » par `true`. Si `x` affirme la proposition `P`,
alors `x = P`.

1. A dit : « Nous sommes tous les deux des menteurs. » Qui est qui ?
2. A dit : « B est un menteur. » B dit : « A et moi sommes de la même espèce. »
3. A dit : « B est un menteur. » B dit : « C est un menteur. » C dit : « A et B sont des menteurs. »

## À prouver
Pour chaque énigme, la **seule** solution possible.

## Ressources
- [Énigmes de chevaliers et de menteurs (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Knights_and_Knaves)

---
*Exercice* `Enigmes.Chevaliers` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Enigmes.Chevaliers` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Enigmes

theorem enigme1 (a b : Bool) (ha : a = (!a && !b)) : a = false ∧ b = true := by
  sorry

theorem enigme2 (a b : Bool) (ha : a = !b) (hb : b = (a == b)) : a = true ∧ b = false := by
  sorry

theorem enigme3 (a b c : Bool) (ha : a = !b) (hb : b = !c) (hc : c = (!a && !b)) :
    a = false ∧ b = true ∧ c = false := by
  sorry

end Parcours.Enigmes

#verifier
