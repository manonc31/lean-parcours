/- @parcours
titre: aⁿbⁿ n'est pas régulier
difficulte: 5
genre: boss
solution: non
requiert: Informatique.Automates, Combinatoire.Tiroirs
indice: Un automate à `k` états lit les mots `aⁱ` pour `i = 0, 1, …, k`. Par le principe des tiroirs, deux d'entre eux (`i < j`) mènent au même état.
indice: Alors `aⁱbⁱ` et `aʲbⁱ` mènent au même état final : l'automate accepte les deux ou aucun. Contradiction.
indice: Lemme utile : `A.lire e (u ++ v) = A.lire (A.lire e u) v`.
-/
import Solutions.Informatique.Automates
import Solutions.Combinatoire.Tiroirs

/-!
# 💀 aⁿbⁿ n'est pas régulier

Le langage `{aⁿbⁿ | n ≥ 0}` (autant de `a` que de `b`, les `a` d'abord) ne peut être reconnu par
**aucun** automate fini : un automate a une mémoire finie, il ne peut pas « compter » jusqu'à `n`.
C'est le lemme de l'étoile (*pumping lemma*), et la raison pour laquelle les expressions régulières
ne savent pas vérifier les parenthèses bien équilibrées.

On code `a` par `false` et `b` par `true`, et « automate fini » par « états = `Fin k` ».

Boss sans solution de référence.

## À prouver
`anbn_non_regulier (k : Nat) (A : Automate (Fin k) Bool) :
  ¬∀ w, A.accepte w = true ↔ ∃ n, w = List.replicate n false ++ List.replicate n true`
-/

namespace Parcours.Info

theorem anbn_non_regulier (k : Nat) (A : Automate (Fin k) Bool) :
    ¬∀ w, A.accepte w = true ↔ ∃ n, w = List.replicate n false ++ List.replicate n true := by -- @exo
  sorry

end Parcours.Info

#verifier
