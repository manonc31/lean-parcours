/- @parcours
titre: Chevaliers et menteurs
difficulte: 2
requiert: Logique.Bilan
indice: Chaque habitant est `true` (chevalier) ou `false` (menteur). « `x` affirme `P` » se traduit par `x = P` : un chevalier dit vrai, un menteur dit faux.
indice: Il n'y a que 4 (ou 8) cas : `revert a b` remet `a` et `b` dans le but (`∀ a b, …`), puis `decide` examine tous les cas.
-/
import Solutions.Logique.Bilan

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
-/

namespace Parcours.Enigmes

theorem enigme1 (a b : Bool) (ha : a = (!a && !b)) : a = false ∧ b = true := by -- @exo
  revert a b
  decide

theorem enigme2 (a b : Bool) (ha : a = !b) (hb : b = (a == b)) : a = true ∧ b = false := by -- @exo
  revert a b
  decide

theorem enigme3 (a b c : Bool) (ha : a = !b) (hb : b = !c) (hc : c = (!a && !b)) :
    a = false ∧ b = true ∧ c = false := by -- @exo
  revert a b c
  decide

end Parcours.Enigmes

#verifier
