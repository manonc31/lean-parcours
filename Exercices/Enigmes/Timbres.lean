import Exercices.Recurrence.Definitions

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

---
*Exercice* `Enigmes.Timbres` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Enigmes.Timbres` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Enigmes

theorem timbres (n : Nat) (h : 8 ≤ n) : ∃ a b, n = 3 * a + 5 * b := by
  sorry

theorem pas_sept : ¬ ∃ a b, 7 = 3 * a + 5 * b := by
  sorry

end Parcours.Enigmes

#verifier
