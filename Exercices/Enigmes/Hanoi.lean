import Exercices.Recurrence.Definitions
import Exercices.Listes.Pont

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

---
*Exercice* `Enigmes.Hanoi` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Enigmes.Hanoi` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Enigmes

/-- Les déplacements (de, vers) pour amener `n` disques de `a` à `c` en passant par `b`. -/
def hanoi : Nat → Nat → Nat → Nat → List (Nat × Nat)
  | 0, _, _, _ => []
  | n + 1, a, b, c => hanoi n a c b ++ [(a, c)] ++ hanoi n b a c

theorem longueur_hanoi (n a b c : Nat) : (hanoi n a b c).length + 1 = 2 ^ n := by
  sorry

end Parcours.Enigmes

#verifier
