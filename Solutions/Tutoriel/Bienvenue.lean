/- @parcours
titre: Bienvenue ! Ta première preuve
difficulte: 1
indice: Le but affiché dans l'infoview est `x = x`. Une égalité de la forme « truc = le même truc » se prouve avec la tactique `rfl`.
indice: Remplace la ligne `sorry` par `rfl`.
-/
import ParcoursOutils

/-!
# Bienvenue dans le parcours Lean !

Chaque exercice est un fichier comme celui-ci : un énoncé en haut, puis un ou plusieurs
théorèmes dont la preuve est remplacée par `sorry` (« désolé, je n'ai pas encore prouvé ça »).
**Ton travail : remplacer chaque `sorry` par une vraie preuve.**

## Comment ça marche
1. Ouvre l'**infoview** de Lean (dans VS Code : `Ctrl+Shift+Enter` / `Cmd+Shift+Enter`,
   ou l'icône ∀ en haut à droite). Elle affiche l'**état de la preuve** là où se trouve ton curseur :
   les hypothèses au-dessus, et le **but** (ce qu'il reste à prouver) après le symbole `⊢`.
2. Place ton curseur sur le `sorry` : l'infoview affiche `⊢ x = x`.
3. Une preuve « en mode tactique » (après `by`) est une suite d'instructions qui transforment
   le but jusqu'à le faire disparaître. La première tactique : **`rfl`** (réflexivité), qui prouve
   tout but de la forme `a = a`.
4. Quand c'est fini, l'infoview affiche « No goals », et le message de `#verifier`
   tout en bas du fichier (clique sur la ligne `#verifier`) te dit si l'exercice est réussi.

## Les symboles
- ✅ réussi · ⭐ réussi **et pur** (sans emprunter de théorème de la bibliothèque pas encore débloqué)
- 🎯 disponible · 🔒 verrouillé (il faut d'abord finir les exercices dont il dépend)

Dans le terminal : `./parcours` te dit ce que tu peux faire ensuite, et
`./parcours verifier` met à jour ta progression.

## Ressources
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/) — le livre de référence (en anglais).
- [Le Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4) — la même philosophie, dans le navigateur.
- Le fichier `AIDE_TACTIQUES.md` à la racine du parcours : toutes les tactiques utiles, en français.
-/

namespace Parcours.Tutoriel

theorem premier_pas (x : Nat) : x = x := by -- @exo
  rfl

end Parcours.Tutoriel

#verifier
