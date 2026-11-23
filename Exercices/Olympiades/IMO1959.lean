import Exercices.Arithmetique.PgcdDivise

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

---
*Exercice* `Olympiades.IMO1959` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Olympiades.IMO1959` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Olymp

open Parcours.Arith

theorem imo1959 (n : Nat) : pgcd (21 * n + 4) (14 * n + 3) = 1 := by
  sorry

end Parcours.Olymp

#verifier
