/- @parcours
titre: IMO 1959, problème 1
difficulte: 3
requiert: Arithmetique.DiviseOrdre
indice: Soit `d = pgcd (21n + 4) (14n + 3)`. Il divise les deux nombres (`pgcd_divise`).
indice: Remarque : `3 × (14n + 3) = 2 × (21n + 4) + 1`. Donc `d` divise `1` (`divise_mul_droite`, `divise_sub`).
indice: Et `d ∣ 1` donne `d = 1` (`divise_un`).
-/
import Solutions.Arithmetique.PgcdDivise

/-!
# IMO 1959, problème 1

Le tout premier problème de la toute première Olympiade Internationale de Mathématiques
(Roumanie, 1959) :

> Montrer que la fraction `(21n + 4) / (14n + 3)` est irréductible pour tout entier naturel `n`.

Autrement dit, le PGCD du numérateur et du dénominateur vaut 1. Tu as tous les outils
(branche Arithmétique).

## À prouver
`imo1959 (n : Nat) : pgcd (21 * n + 4) (14 * n + 3) = 1`

## Ressources
- [Olympiades internationales de mathématiques (Wikipédia)](https://fr.wikipedia.org/wiki/Olympiades_internationales_de_math%C3%A9matiques)
-/

namespace Parcours.Olymp

open Parcours.Arith

theorem imo1959 (n : Nat) : pgcd (21 * n + 4) (14 * n + 3) = 1 := by -- @exo
  obtain ⟨h1, h2⟩ := pgcd_divise (21 * n + 4) (14 * n + 3)
  have ha := divise_mul_droite h1 2
  have hb := divise_mul_droite h2 3
  rw [show (14 * n + 3) * 3 = (21 * n + 4) * 2 + 1 by omega] at hb
  exact divise_un (divise_sub hb ha)

end Parcours.Olymp

#verifier
