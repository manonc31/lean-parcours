import Exercices.Programmes.Definitions

/-!
# Le nombre de chiffres

Combien de chiffres a un nombre en base 10 ? On divise par 10 jusqu'à tomber sous 10.
La spécification : un nombre à `c` chiffres est entre `10^(c−1)` et `10^c`.

## À prouver
1. `nbChiffres_pos : 1 ≤ nbChiffres n`
2. `lt_puissance : n < 10 ^ nbChiffres n`
3. `puissance_le : 0 < n → 10 ^ (nbChiffres n - 1) ≤ n`

---
*Exercice* `Programmes.Chiffres` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Programmes.Chiffres` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

def nbChiffres (n : Nat) : Nat := if n < 10 then 1 else nbChiffres (n / 10) + 1
termination_by n
decreasing_by omega

theorem nbChiffres_pos (n : Nat) : 1 ≤ nbChiffres n := by
  sorry

theorem lt_puissance (n : Nat) : n < 10 ^ nbChiffres n := by
  sorry

theorem puissance_le (n : Nat) (h : 0 < n) : 10 ^ (nbChiffres n - 1) ≤ n := by
  sorry

end Parcours.Prog

#verifier
