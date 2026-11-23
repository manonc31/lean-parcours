/- @parcours
titre: Le pont arithmétique
difficulte: 3
genre: pont
debloque: divisibilite
permis: Nat.gcd*
requiert: Arithmetique.LemmeEuclide, Arithmetique.Unicite, Arithmetique.Congruences
indice: `fun_induction pgcd a b with`. Cas 1 : `Nat.gcd_zero_right`.
indice: Cas 2 : il faut `Nat.gcd a b = Nat.gcd b (a % b)`. `Nat.gcd_rec m n : gcd m n = gcd (n % m) m` et `Nat.gcd_comm`.
indice: `rw [ih, Nat.gcd_comm a b, Nat.gcd_rec b a, Nat.gcd_comm]`.
-/
import Solutions.Arithmetique.PgcdDivise

/-!
# 🌉 Le pont arithmétique

Ton `pgcd` est le `Nat.gcd` de Lean. Dans cet exercice (et seulement lui), tu as le droit
aux lemmes `Nat.gcd_*` de la bibliothèque pour faire le lien.

🔑 **Récompense** : débloque le jeton **`divisibilite`** : tous les lemmes de la bibliothèque
sur `∣`, `Nat.gcd`, `Nat.lcm`, `Nat.Coprime`… deviennent purs pour la suite.

## À prouver
`pgcd_eq_gcd (a b : Nat) : pgcd a b = Nat.gcd a b`
-/

namespace Parcours.Arith

theorem pgcd_eq_gcd (a b : Nat) : pgcd a b = Nat.gcd a b := by -- @exo
  fun_induction pgcd a b with
  | case1 a => rw [Nat.gcd_zero_right]
  | case2 a b hb ih => rw [ih, Nat.gcd_comm a b, Nat.gcd_rec b a, Nat.gcd_comm]

end Parcours.Arith

#verifier
