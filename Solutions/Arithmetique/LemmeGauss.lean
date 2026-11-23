/- @parcours
titre: Le lemme de Gauss
difficulte: 3
indice: `a` divise `a * c` et `b * c`, donc il divise leur PGCD (`divise_pgcd`).
indice: Et `pgcd (a * c) (b * c) = pgcd a b * c = 1 * c = c` (`pgcd_mul_droite`).
-/
import Solutions.Arithmetique.PgcdMul

/-!
# Le lemme de Gauss

> Si `a` divise `b·c` et que `a` est premier avec `b`, alors `a` divise `c`.

## À prouver
`lemme_gauss : a ∣ b * c → pgcd a b = 1 → a ∣ c`

## Ressources
- [Lemme de Gauss (Wikipédia)](https://fr.wikipedia.org/wiki/Lemme_de_Gauss)
-/

namespace Parcours.Arith

theorem lemme_gauss {a b c : Nat} (h : a ∣ b * c) (hab : pgcd a b = 1) : a ∣ c := by -- @exo
  have h1 : a ∣ pgcd (a * c) (b * c) := divise_pgcd (divise_mul_droite (divise_refl a) c) h
  rw [pgcd_mul_droite, hab, Nat.one_mul] at h1
  exact h1

end Parcours.Arith

#verifier
