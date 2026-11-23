import Exercices.Naturels.AddRightComm
import Exercices.Naturels.Successeur

/-!
# Pair ou impair

On définit : `n` est **pair** s'il existe `k` avec `n = k + k`.

## À prouver
1. `pair_add : Pair a → Pair b → Pair (a + b)`
2. `pair_ou_impair (n : ℕ) : Pair n ∨ Pair (succ n)` (tout entier est pair, ou son successeur l'est)

---
*Exercice* `Naturels.Parite` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Naturels.Parite` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

def Pair (n : ℕ) : Prop := ∃ k, n = k + k

theorem pair_add {a b : ℕ} (ha : Pair a) (hb : Pair b) : Pair (a + b) := by
  sorry

theorem pair_ou_impair (n : ℕ) : Pair n ∨ Pair (succ n) := by
  sorry

end Parcours.ℕ

#verifier
