import Exercices.Arithmetique.DiviseOrdre

/-!
# Le PGCD divise

Montre que l'algorithme d'Euclide calcule bien un diviseur commun… et même le **plus grand**,
au sens où tout diviseur commun le divise.

## À prouver
1. `divise_de_mod : d ∣ b → d ∣ a % b → d ∣ a`
2. `divise_mod : d ∣ a → d ∣ b → d ∣ a % b`
3. `pgcd_divise (a b : Nat) : pgcd a b ∣ a ∧ pgcd a b ∣ b`
4. `divise_pgcd : d ∣ a → d ∣ b → d ∣ pgcd a b`

---
*Exercice* `Arithmetique.PgcdDivise` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Arithmetique.PgcdDivise` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Arith

theorem divise_de_mod {d a b : Nat} (h1 : d ∣ b) (h2 : d ∣ a % b) : d ∣ a := by
  sorry

theorem divise_mod {d a b : Nat} (h1 : d ∣ a) (h2 : d ∣ b) : d ∣ a % b := by
  sorry

theorem pgcd_divise (a b : Nat) : pgcd a b ∣ a ∧ pgcd a b ∣ b := by
  sorry

theorem divise_pgcd {d a b : Nat} (h1 : d ∣ a) (h2 : d ∣ b) : d ∣ pgcd a b := by
  sorry

end Parcours.Arith

#verifier
