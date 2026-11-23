import Exercices.Informatique.Automates
import Exercices.Combinatoire.Tiroirs

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

---
*Exercice* `Informatique.AnBn` · difficulté ★★★★★

💡 Indices : `./parcours indice Informatique.AnBn` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Info

theorem anbn_non_regulier (k : Nat) (A : Automate (Fin k) Bool) :
    ¬∀ w, A.accepte w = true ↔ ∃ n, w = List.replicate n false ++ List.replicate n true := by
  sorry

end Parcours.Info

#verifier
