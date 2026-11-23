import Exercices.Recurrence.Definitions

/-!
# 💀 Le théorème de Goodstein

Écris un nombre en base 2 « héréditaire » (même les exposants sont écrits en base 2) :
`266 = 2^(2^(2+1)) + 2^(2+1) + 2`. Remplace tous les 2 par des 3, puis retire 1. Recommence avec
la base 4, puis 5… Les nombres explosent : partant de 4, la suite atteint des valeurs astronomiques
(elle met environ `3 × 2^402653211` étapes à revenir à 0).

**Théorème** (Goodstein, 1944) : la suite finit **toujours** par atteindre 0.

Le plus fou : Kirby et Paris (1982) ont prouvé que ce théorème **ne peut pas être démontré dans
l'arithmétique de Peano**, malgré son énoncé purement arithmétique ! Il faut les ordinaux infinis.
Lean, lui, est assez puissant pour le faire.

Boss sans solution de référence. Un des plus profonds du parcours.

## À prouver
`goodstein_termine (m : Nat) : ∃ k, goodstein m k = 0`

## Ressources
- [Théorème de Goodstein (Wikipédia)](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_de_Goodstein)

---
*Exercice* `Terminaison.Goodstein` · difficulté ★★★★★

💡 Indices : `./parcours indice Terminaison.Goodstein` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Term

/-- `logb b f n` : le plus grand `e` tel que `b ^ e ≤ n` (avec `f` unités de carburant). -/
def logb (b : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, n => if b ≤ 1 ∨ n < b then 0 else logb b f (n / b) + 1

/-- Écrit `n` en base `b` héréditaire et remplace `b` par `b + 1` partout (avec carburant). -/
def changeBaseF (b : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, n =>
    if n = 0 then 0 else
      let e := logb b n n
      let p := b ^ e
      (b + 1) ^ changeBaseF b f e * (n / p) + changeBaseF b f (n % p)

def changeBase (b n : Nat) : Nat := changeBaseF b (n + 1) n

/-- La suite de Goodstein partant de `m`. -/
def goodstein (m : Nat) : Nat → Nat
  | 0 => m
  | k + 1 => changeBase (k + 2) (goodstein m k) - 1

example : (List.range 6).map (goodstein 3) = [3, 3, 3, 2, 1, 0] := by decide

theorem goodstein_termine (m : Nat) : ∃ k, goodstein m k = 0 := by
  sorry

end Parcours.Term

#verifier
