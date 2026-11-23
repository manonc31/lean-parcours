/- @parcours
titre: Le calendrier perpétuel
difficulte: 2
requiert: Enigmes.Vendredi13
indice: Pour les dates : `decide`.
indice: Pour `periode` : `unfold zeller`, `by_cases h : m ≤ 2` (janvier-février ou non), `simp only [h, ↓reduceIte]`. `omega` a besoin d'aide : prouve d'abord que `(x + 400) % 100 = x % 100` et `(x + 400) / 100 / 4 = x / 100 / 4 + 1`, et réécris avec (`a % 100` ne change pas, `a / 100` augmente de 4).
-/
import Solutions.Listes.Pont
import Solutions.Recurrence.Definitions

/-!
# Le calendrier perpétuel

La **congruence de Zeller** donne le jour de la semaine de n'importe quelle date (calendrier
grégorien) : `0` = samedi, `1` = dimanche, `2` = lundi, `3` = mardi… Janvier et février comptent
comme les mois 13 et 14 de l'année précédente (pour que le 29 février soit à la fin).

## À prouver
1. `bastille` : le 14 juillet 1789 était un mardi.
2. `an_2000` : le 1ᵉʳ janvier 2000 était un samedi.
3. `periode : zeller j m (a + 400) = zeller j m a` : le calendrier se répète tous les 400 ans.

## Ressources
- [Congruence de Zeller (Wikipédia)](https://fr.wikipedia.org/wiki/Congruence_de_Zeller)
-/

namespace Parcours.Enigmes

def zeller (jour mois annee : Nat) : Nat :=
  let m := if mois ≤ 2 then mois + 12 else mois
  let a := if mois ≤ 2 then annee - 1 else annee
  (jour + 13 * (m + 1) / 5 + a % 100 + a % 100 / 4 + a / 100 / 4 + 5 * (a / 100)) % 7

theorem bastille : zeller 14 7 1789 = 3 := by -- @exo
  decide

theorem an_2000 : zeller 1 1 2000 = 0 := by -- @exo
  decide

theorem periode (j m a : Nat) (ha : 1 ≤ a) : zeller j m (a + 400) = zeller j m a := by -- @exo
  have cle : ∀ x : Nat, (x + 400) % 100 = x % 100 ∧ (x + 400) / 100 / 4 = x / 100 / 4 + 1 ∧
      5 * ((x + 400) / 100) = 5 * (x / 100) + 20 := by
    intro x
    omega
  unfold zeller
  by_cases h : m ≤ 2 <;> simp only [h, ↓reduceIte]
  · rw [show a + 400 - 1 = (a - 1) + 400 by omega]
    obtain ⟨k1, k2, k3⟩ := cle (a - 1)
    rw [k1, k2, k3]
    omega
  · obtain ⟨k1, k2, k3⟩ := cle a
    rw [k1, k2, k3]
    omega

end Parcours.Enigmes

#verifier
