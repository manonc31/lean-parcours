import Exercices.Programmes.Definitions

/-!
# Les années bissextiles

Une année est bissextile si elle est divisible par 4, sauf les siècles, sauf les multiples
de 400 : 2000 l'était, 1900 non, 2024 oui. Le calendrier grégorien se répète tous les 400 ans…
et 400 ans font **exactement** un nombre entier de semaines ! (Donc le 1er janvier 2400 sera un
samedi, comme le 1er janvier 2000.)

## À prouver
1. `an2000`, `an1900` : 2000 est bissextile, 1900 ne l'est pas.
2. `periode : bissextile (a + 400) = bissextile a`
3. `quatre_cents_ans` : 97 années bissextiles sur 400 ans.
4. `semaines` : 400 ans font 146 097 jours, un multiple de 7.

## Ressources
- [Année bissextile (Wikipédia)](https://fr.wikipedia.org/wiki/Ann%C3%A9e_bissextile)

---
*Exercice* `Programmes.Bissextile` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Programmes.Bissextile` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

def bissextile (a : Nat) : Bool := (a % 4 == 0 && a % 100 != 0) || a % 400 == 0

def jours (a : Nat) : Nat := if bissextile a then 366 else 365

theorem an2000 : bissextile 2000 = true := by
  sorry

theorem an1900 : bissextile 1900 = false := by
  sorry

theorem periode (a : Nat) : bissextile (a + 400) = bissextile a := by
  sorry

theorem quatre_cents_ans : ((List.range 400).filter bissextile).length = 97 := by
  sorry

theorem semaines : ((List.range 400).map jours).sum = 146097 ∧ 146097 % 7 = 0 := by
  sorry

end Parcours.Prog

#verifier
