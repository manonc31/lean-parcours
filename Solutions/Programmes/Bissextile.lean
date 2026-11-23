/- @parcours
titre: Les années bissextiles
difficulte: 1
requiert: Programmes.FizzBuzz
indice: Les calculs sur des valeurs précises : `decide` (ou `decide +kernel` si c'est gros).
indice: Pour `periode` : `(a + 400) % 4 = a % 4` (`omega`), pareil pour 100 et 400, puis `simp only [bissextile, …]`.
-/
import Solutions.Programmes.Definitions

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
-/

namespace Parcours.Prog

def bissextile (a : Nat) : Bool := (a % 4 == 0 && a % 100 != 0) || a % 400 == 0

def jours (a : Nat) : Nat := if bissextile a then 366 else 365

theorem an2000 : bissextile 2000 = true := by -- @exo
  decide

theorem an1900 : bissextile 1900 = false := by -- @exo
  decide

theorem periode (a : Nat) : bissextile (a + 400) = bissextile a := by -- @exo
  have h1 : (a + 400) % 4 = a % 4 := by omega
  have h2 : (a + 400) % 100 = a % 100 := by omega
  have h3 : (a + 400) % 400 = a % 400 := by omega
  simp only [bissextile, h1, h2, h3]

theorem quatre_cents_ans : ((List.range 400).filter bissextile).length = 97 := by -- @exo
  decide

theorem semaines : ((List.range 400).map jours).sum = 146097 ∧ 146097 % 7 = 0 := by -- @exo
  decide +kernel

end Parcours.Prog

#verifier
