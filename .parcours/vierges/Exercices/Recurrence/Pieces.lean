import Exercices.Recurrence.Definitions

/-!
# Le problème des pièces

Avec des pièces de 3 € et de 5 €, on peut payer n'importe quelle somme d'au moins 8 €.
(7 € est le plus grand montant impossible : c'est le **nombre de Frobenius** de 3 et 5.)

Nouveauté : en Lean, un théorème peut être une **fonction récursive** : il s'appelle lui-même sur
un plus petit argument. C'est exactement une récurrence forte ! Lean vérifie que l'argument
diminue (ici `n + 8 < n + 11`).

## À prouver
`pieces : (n : Nat) → 8 ≤ n → ∃ a b, n = 3 * a + 5 * b`

## Ressources
- [Problème des pièces de monnaie (Wikipédia)](https://fr.wikipedia.org/wiki/Probl%C3%A8me_des_pi%C3%A8ces_de_monnaie)

---
*Exercice* `Recurrence.Pieces` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Recurrence.Pieces` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Recurrence

theorem pieces : (n : Nat) → 8 ≤ n → ∃ a b, n = 3 * a + 5 * b :=
  sorry

end Parcours.Recurrence

#verifier
