/- @parcours
titre: Syracuse pour les petits nombres
difficulte: 2
indice: L'énoncé est un calcul sur un nombre fini de cas : `decide` le vérifie entièrement !
indice: Si tu es curieux, `#eval (List.range 30).map (fun n => arrive 200 (n + 1))` montre le détail.
-/
import Solutions.Recurrence.Definitions

/-!
# Syracuse pour les petits nombres

La suite de Syracuse (ou de Collatz) : si `n` est pair on le divise par 2, sinon on le remplace
par `3n + 1`. Partant de 27 : 27, 82, 41, 124, 62, 31, 94, … elle monte jusqu'à 9 232 et met
111 étapes pour atteindre 1.

**Conjecture** (1937, toujours ouverte !) : on finit toujours par atteindre 1. Elle a été vérifiée
par ordinateur jusqu'à environ 2⁷¹. Ici, vérifie-la (avec Lean) pour `1 ≤ n ≤ 30`.
La version générale t'attend dans la branche des problèmes ouverts…

`arrive f n` : partant de `n`, atteint-on 1 en au plus `f` étapes ?

## À prouver
`syracuse_petits : (List.range 30).all (fun n => arrive 200 (n + 1)) = true`

## Ressources
- [Conjecture de Syracuse (Wikipédia)](https://fr.wikipedia.org/wiki/Conjecture_de_Syracuse)
-/

namespace Parcours.Term

def collatz (n : Nat) : Nat := if n % 2 = 0 then n / 2 else 3 * n + 1

def arrive : Nat → Nat → Bool
  | 0, _ => false
  | f + 1, n => n == 1 || arrive f (collatz n)

theorem syracuse_petits : (List.range 30).all (fun n => arrive 200 (n + 1)) = true := by -- @exo
  decide

end Parcours.Term

#verifier
