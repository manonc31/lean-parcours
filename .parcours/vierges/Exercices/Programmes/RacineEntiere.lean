import Exercices.Programmes.Definitions

/-!
# La racine carrée entière

`racine n` est le plus grand entier `r` tel que `r² ≤ n`. Le programme essaie `n, n − 1, …`
jusqu'à trouver un `r` qui convient (lent, mais facile à prouver !).

## À prouver
1. `racineAux_le : (racineAux n k)² ≤ n`
2. `racineAux_lt : n < (k + 1)² → n < (racineAux n k + 1)²`
3. `racine_spec : r * r ≤ n ∧ n < (r + 1) * (r + 1)` où `r = racine n`
4. `racine_mille : racine 1000 = 31`

---
*Exercice* `Programmes.RacineEntiere` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Programmes.RacineEntiere` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

def racineAux (n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => if (k + 1) * (k + 1) ≤ n then k + 1 else racineAux n k

def racine (n : Nat) : Nat := racineAux n n

theorem racineAux_le (n k : Nat) : racineAux n k * racineAux n k ≤ n := by
  sorry

theorem racineAux_lt (n k : Nat) (h : n < (k + 1) * (k + 1)) :
    n < (racineAux n k + 1) * (racineAux n k + 1) := by
  sorry

theorem racine_spec (n : Nat) :
    racine n * racine n ≤ n ∧ n < (racine n + 1) * (racine n + 1) := by
  sorry

theorem racine_mille : racine 1000 = 31 := by
  sorry

end Parcours.Prog

#verifier
