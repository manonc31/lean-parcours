import Exercices.Programmes.Definitions

/-!
# Changer de base

Écrire un nombre en base `b` : les chiffres sont les restes successifs de la division par `b`
(chiffre des unités en tête). Puis relire la liste de chiffres pour retrouver le nombre.
`versBase 2 13 = [1, 0, 1, 1]` (car 13 = 1101 en binaire).

## À prouver
1. `aller_retour : depuisBase b (versBase b n) = n` (pour `b ≥ 2`)
2. `chiffres_petits : d ∈ versBase b n → d < b`

---
*Exercice* `Programmes.Bases` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Programmes.Bases` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

def versBase (b n : Nat) : List Nat :=
  if h : 2 ≤ b ∧ 0 < n then n % b :: versBase b (n / b) else []
termination_by n
decreasing_by exact Nat.div_lt_self h.2 (by omega)

def depuisBase (b : Nat) : List Nat → Nat
  | [] => 0
  | d :: l => d + b * depuisBase b l

theorem aller_retour (b n : Nat) (hb : 2 ≤ b) : depuisBase b (versBase b n) = n := by
  sorry

theorem chiffres_petits (b n : Nat) : ∀ d ∈ versBase b n, d < b := by
  sorry

end Parcours.Prog

#verifier
