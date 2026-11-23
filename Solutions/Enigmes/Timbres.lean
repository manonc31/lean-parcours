/- @parcours
titre: Les timbres de 3 et 5
difficulte: 2
requiert: Enigmes.CentOiseaux
indice: Trois cas selon `n % 3`. Si `n % 3 = 1`, utilise deux timbres de 5 (`n − 10` est multiple de 3).
indice: Pour donner les témoins : `exact ⟨n / 3, 0, by omega⟩`.
-/
import Solutions.Recurrence.Definitions

/-!
# Les timbres de 3 et 5

Avec des timbres de 3 € et de 5 €, quels affranchissements peut-on faire exactement ?
1, 2, 4 et 7 sont impossibles, mais **tout** montant à partir de 8 est possible.
(En général, avec `a` et `b` premiers entre eux, le plus grand montant impossible est `ab − a − b`.)

## À prouver
1. `timbres : 8 ≤ n → ∃ a b, n = 3 * a + 5 * b`
2. `pas_sept : ¬ ∃ a b, 7 = 3 * a + 5 * b`

## Ressources
- [Problème des pièces de monnaie de Frobenius (Wikipédia)](https://fr.wikipedia.org/wiki/Probl%C3%A8me_des_pi%C3%A8ces_de_monnaie)
-/

namespace Parcours.Enigmes

theorem timbres (n : Nat) (h : 8 ≤ n) : ∃ a b, n = 3 * a + 5 * b := by -- @exo
  have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases this with h3 | h3 | h3
  · exact ⟨n / 3, 0, by omega⟩
  · exact ⟨(n - 10) / 3, 2, by omega⟩
  · exact ⟨(n - 5) / 3, 1, by omega⟩

theorem pas_sept : ¬ ∃ a b, 7 = 3 * a + 5 * b := by -- @exo
  rintro ⟨a, b, h⟩
  omega

end Parcours.Enigmes

#verifier
