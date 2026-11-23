import Exercices.Informatique.Regex

/-!
# 💀 L'algorithme de Brzozowski

La **dérivée** d'une expression `r` par une lettre `a` est une expression `deriv a r` qui reconnaît
les mots `w` tels que `r` reconnaît `a :: w`. Pour tester si `r` reconnaît un mot, on dérive lettre
par lettre, puis on teste `nullable` : c'est un algorithme élégant (Brzozowski, 1964), sans automate.

Boss sans solution de référence.

## À prouver
`correspond_correct (r : Regex α) (w : List α) : correspond r w = true ↔ Reconnait r w`

## Ressources
- [Dérivée de Brzozowski (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Brzozowski_derivative)

---
*Exercice* `Informatique.Brzozowski` · difficulté ★★★★★

💡 Indices : `./parcours indice Informatique.Brzozowski` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Info

open Regex

variable {α : Type} [DecidableEq α]

def deriv (a : α) : Regex α → Regex α
  | vide => vide
  | eps => vide
  | car b => if a = b then eps else vide
  | union r s => union (deriv a r) (deriv a s)
  | concat r s => if nullable r then union (concat (deriv a r) s) (deriv a s) else concat (deriv a r) s
  | etoile r => concat (deriv a r) (etoile r)

def correspond (r : Regex α) : List α → Bool
  | [] => nullable r
  | a :: w => correspond (deriv a r) w

theorem correspond_correct (r : Regex α) (w : List α) : correspond r w = true ↔ Reconnait r w := by
  sorry

end Parcours.Info

#verifier
