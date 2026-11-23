/- @parcours
titre: Les pages du livre
difficulte: 2
requiert: Enigmes.CentOiseaux
indice: `croissant` : récurrence sur `k`.
indice: `formule` : récurrence sur `k` ; la page `100 + k` a 3 chiffres.
indice: `livre` : si `n < 99`, le livre a au plus 189 chiffres ; sinon, utilise `formule (n - 99)`.
-/
import Solutions.Recurrence.Definitions

/-!
# Les pages du livre

Pour numéroter les pages d'un livre (à partir de 1), un imprimeur a utilisé 1 095 chiffres.
Combien de pages a le livre ?

## Se le représenter
Pages 1 à 9 : 9 chiffres. Pages 10 à 99 : `90 × 2 = 180` chiffres. Ensuite, 3 chiffres par page :
`1095 − 189 = 906 = 3 × 302`. Donc `99 + 302 = 401` pages.

## À prouver
1. `croissant : chiffresLivre m ≤ chiffresLivre (m + k)`
2. `formule : chiffresLivre (99 + k) = 189 + 3k` (pour `k ≤ 900`)
3. `livre : chiffresLivre n = 1095 ↔ n = 401` (pour `n ≤ 999`)
-/

namespace Parcours.Enigmes

def chiffresPage (p : Nat) : Nat := if p < 10 then 1 else if p < 100 then 2 else 3

def chiffresLivre : Nat → Nat
  | 0 => 0
  | n + 1 => chiffresLivre n + chiffresPage (n + 1)

theorem croissant (m k : Nat) : chiffresLivre m ≤ chiffresLivre (m + k) := by -- @exo
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    rw [← Nat.add_assoc, chiffresLivre]
    omega

theorem formule (k : Nat) (hk : k ≤ 900) : chiffresLivre (99 + k) = 189 + 3 * k := by -- @exo
  induction k with
  | zero => decide
  | succ k ih =>
    rw [← Nat.add_assoc, chiffresLivre, ih (by omega)]
    have : chiffresPage (99 + k + 1) = 3 := by
      unfold chiffresPage
      split
      · omega
      · split
        · omega
        · rfl
    omega

theorem livre (n : Nat) (hn : n ≤ 999) : chiffresLivre n = 1095 ↔ n = 401 := by -- @exo
  constructor
  · intro h
    by_cases h' : n < 99
    · have := croissant n (99 - n)
      rw [show n + (99 - n) = 99 by omega, show chiffresLivre 99 = 189 by decide] at this
      omega
    · have := formule (n - 99) (by omega)
      rw [show 99 + (n - 99) = n by omega] at this
      omega
  · rintro rfl
    exact formule 302 (by omega)

end Parcours.Enigmes

#verifier
