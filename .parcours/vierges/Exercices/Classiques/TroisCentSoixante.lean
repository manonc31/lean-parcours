import Exercices.Listes.Pont
import Exercices.Recurrence.Definitions

/-!
# Pourquoi 360 degrés ?

## Se le représenter
Les Babyloniens ont choisi de diviser le cercle en 360 degrés. Une bonne raison : 360 a énormément
de diviseurs (24 : on peut partager un tour en 2, 3, 4, 5, 6, 8, 9, 10, 12… parts égales), plus
que tout nombre plus petit. C'est un nombre « hautement composé ».

## À prouver
1. `diviseurs_360 : nbDiviseurs 360 = 24`
2. `record : ∀ n < 360, nbDiviseurs n < 24`

## Ressources
- [Nombre hautement composé (Wikipédia)](https://fr.wikipedia.org/wiki/Nombre_hautement_compos%C3%A9)

---
*Exercice* `Classiques.TroisCentSoixante` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Classiques.TroisCentSoixante` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

def nbDiviseurs (n : Nat) : Nat := ((List.range (n + 1)).filter fun d => 0 < d && n % d == 0).length

theorem diviseurs_360 : nbDiviseurs 360 = 24 := by
  sorry

theorem record : ∀ n, n < 360 → nbDiviseurs n < 24 := by
  sorry

end Parcours.Classiques

#verifier
