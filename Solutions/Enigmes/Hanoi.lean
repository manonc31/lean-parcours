/- @parcours
titre: Les tours de Hanoï
difficulte: 2
requiert: Recurrence.Geometrique
indice: Récurrence sur `n` en généralisant les trois piquets (`induction n generalizing a b c`).
indice: Cas `n + 1` : `simp only [hanoi, List.length_append, List.length_singleton, ih]`, puis `Nat.pow_succ` et `omega`.
-/
import Solutions.Recurrence.Definitions
import Solutions.Listes.Pont

/-!
# Les tours de Hanoï

Déplacer une tour de `n` disques du piquet `a` au piquet `c` (en s'aidant de `b`), un disque à la
fois, sans jamais poser un disque sur un plus petit. La solution récursive : déplacer les `n - 1`
disques du haut vers `b`, puis le grand disque vers `c`, puis les `n - 1` disques de `b` vers `c`.

Combien de déplacements ? `2ⁿ - 1`. La légende dit que des moines déplacent 64 disques d'or :
à un disque par seconde, il leur faudra 585 milliards d'années.

## À prouver
`longueur_hanoi : (hanoi n a b c).length + 1 = 2 ^ n`

## Ressources
- [Tours de Hanoï (Wikipédia)](https://fr.wikipedia.org/wiki/Tours_de_Hano%C3%AF)
-/

namespace Parcours.Enigmes

/-- Les déplacements (de, vers) pour amener `n` disques de `a` à `c` en passant par `b`. -/
def hanoi : Nat → Nat → Nat → Nat → List (Nat × Nat)
  | 0, _, _, _ => []
  | n + 1, a, b, c => hanoi n a c b ++ [(a, c)] ++ hanoi n b a c

theorem longueur_hanoi (n a b c : Nat) : (hanoi n a b c).length + 1 = 2 ^ n := by -- @exo
  induction n generalizing a b c with
  | zero => rfl
  | succ n ih =>
    have h1 := ih a c b
    have h2 := ih b a c
    simp only [hanoi, List.length_append, List.length_singleton]
    rw [Nat.pow_succ]
    omega

end Parcours.Enigmes

#verifier
