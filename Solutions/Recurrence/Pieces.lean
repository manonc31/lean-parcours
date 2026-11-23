/- @parcours
titre: Le problème des pièces
difficulte: 3
indice: Écris le théorème comme une fonction récursive : `theorem pieces : (n : Nat) → 8 ≤ n → ∃ a b, n = 3 * a + 5 * b` puis des cas `| 8, _ => …`, `| 9, _ => …`, `| 10, _ => …`, `| n + 11, _ => …`.
indice: Les cas `0` à `7` sont impossibles : `| 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h => absurd h (by omega)`.
indice: Cas `n + 11` : appelle `pieces (n + 8) (by omega)` (un « appel récursif » = l'hypothèse de récurrence forte !) et ajoute une pièce de 3.
-/
import Solutions.Recurrence.Definitions

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
-/

namespace Parcours.Recurrence

theorem pieces : (n : Nat) → 8 ≤ n → ∃ a b, n = 3 * a + 5 * b -- @exo
  | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h => absurd h (by omega)
  | 8, _ => ⟨1, 1, rfl⟩
  | 9, _ => ⟨3, 0, rfl⟩
  | 10, _ => ⟨0, 2, rfl⟩
  | n + 11, _ => by
    obtain ⟨a, b, h⟩ := pieces (n + 8) (by omega)
    exact ⟨a + 1, b, by omega⟩

end Parcours.Recurrence

#verifier
