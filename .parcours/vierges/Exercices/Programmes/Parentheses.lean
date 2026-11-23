import Exercices.Programmes.Definitions

/-!
# Les parenthèses bien équilibrées

Un éditeur de code vérifie que les parenthèses sont bien équilibrées avec un simple
**compteur** : +1 pour « ( », −1 pour « ) », le compteur ne doit jamais devenir négatif et doit
finir à 0. (Ici `true` = « ( » et `false` = « ) ».)

Mais qu'est-ce qu'un « bon parenthésage » ? La définition mathématique est **inductive** : le mot
vide, `( mot )`, ou deux bons mots à la suite. Il faut prouver que le compteur accepte tous les
bons mots.

## À prouver
1. `verif_append` : un bon mot ne change pas l'état du compteur.
2. `verif_correct : BienParenthese l → verif l 0 = true`
3. `exemples` : `(()())` est accepté, `())(` est refusé.

---
*Exercice* `Programmes.Parentheses` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Programmes.Parentheses` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

inductive BienParenthese : List Bool → Prop
  | vide : BienParenthese []
  | entoure {l : List Bool} : BienParenthese l → BienParenthese (true :: l ++ [false])
  | concat {l₁ l₂ : List Bool} : BienParenthese l₁ → BienParenthese l₂ → BienParenthese (l₁ ++ l₂)

def verif : List Bool → Nat → Bool
  | [], c => c == 0
  | true :: l, c => verif l (c + 1)
  | false :: l, c => c != 0 && verif l (c - 1)

theorem verif_append (l : List Bool) (h : BienParenthese l) :
    ∀ (r : List Bool) (c : Nat), verif (l ++ r) c = verif r c := by
  sorry

theorem verif_correct (l : List Bool) (h : BienParenthese l) : verif l 0 = true := by
  sorry

theorem exemples : verif [true, true, false, true, false, false] 0 = true ∧
    verif [true, false, false, true] 0 = false := by
  sorry

end Parcours.Prog

#verifier
