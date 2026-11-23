import Exercices.Naturels.SuccAdd

/-!
# Successeur et « + 1 »

`succ n` et `n + 1` désignent le même entier. Mais pour Lean ce sont deux **expressions**
différentes : l'une est un constructeur, l'autre une addition. Quand c'est vrai « par calcul »,
`rfl` le voit. Sinon, il faut réécrire.

## À prouver
1. `succ_eq_add_one (n : ℕ) : succ n = n + 1`
2. `one_add_eq_succ (n : ℕ) : 1 + n = succ n`

## Rappel
`one_eq_succ_zero : 1 = succ 0`, `succ_add`, `zero_add`.

---
*Exercice* `Naturels.Successeur` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Naturels.Successeur` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

theorem succ_eq_add_one (n : ℕ) : succ n = n + 1 := by
  sorry

theorem one_add_eq_succ (n : ℕ) : 1 + n = succ n := by
  sorry

end Parcours.ℕ

#verifier
