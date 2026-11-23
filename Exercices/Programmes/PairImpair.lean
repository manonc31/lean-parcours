import Exercices.Programmes.Definitions

/-!
# Pair et impair, mutuellement

Deux fonctions qui s'appellent l'une l'autre (**récursion mutuelle**) : `n + 1` est pair si `n`
est impair, et impair si `n` est pair.

## À prouver
`pair_impair : estPair n = (n % 2 == 0) ∧ estImpair n = (n % 2 == 1)`

Il faut prouver les deux en même temps : chacune a besoin de l'autre dans la récurrence.

---
*Exercice* `Programmes.PairImpair` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Programmes.PairImpair` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

mutual
def estPair : Nat → Bool
  | 0 => true
  | n + 1 => estImpair n

def estImpair : Nat → Bool
  | 0 => false
  | n + 1 => estPair n
end

theorem pair_impair (n : Nat) : estPair n = (n % 2 == 0) ∧ estImpair n = (n % 2 == 1) := by
  sorry

end Parcours.Prog

#verifier
