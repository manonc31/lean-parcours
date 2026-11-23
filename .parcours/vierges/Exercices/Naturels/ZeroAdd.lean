import Exercices.Naturels.Base

/-!
# Zéro à gauche

Par définition, `a + 0 = a` (`add_zero`). Mais `0 + a = a` n'est **pas** vrai par définition :
l'addition « regarde » son second argument. Il faut une **récurrence**.

## À prouver
`zero_add (n : ℕ) : 0 + n = n`

## Rappel
- `add_zero a : a + 0 = a`
- `add_succ a b : a + succ b = succ (a + b)`
- `induction n with | zero => … | succ n ih => …`

## Ressources
- [Raisonnement par récurrence (Wikipédia)](https://fr.wikipedia.org/wiki/Raisonnement_par_r%C3%A9currence)

---
*Exercice* `Naturels.ZeroAdd` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Naturels.ZeroAdd` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

theorem zero_add (n : ℕ) : 0 + n = n := by
  sorry

end Parcours.ℕ

#verifier
