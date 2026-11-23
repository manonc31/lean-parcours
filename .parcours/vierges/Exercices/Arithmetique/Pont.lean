import Exercices.Arithmetique.PgcdDivise

/-!
# 🌉 Le pont arithmétique

Ton `pgcd` est le `Nat.gcd` de Lean. Dans cet exercice (et seulement lui), tu as le droit
aux lemmes `Nat.gcd_*` de la bibliothèque pour faire le lien.

🔑 **Récompense** : débloque le jeton **`divisibilite`** : tous les lemmes de la bibliothèque
sur `∣`, `Nat.gcd`, `Nat.lcm`, `Nat.Coprime`… deviennent purs pour la suite.

## À prouver
`pgcd_eq_gcd (a b : Nat) : pgcd a b = Nat.gcd a b`

---
*Exercice* `Arithmetique.Pont` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Arithmetique.Pont` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Arith

theorem pgcd_eq_gcd (a b : Nat) : pgcd a b = Nat.gcd a b := by
  sorry

end Parcours.Arith

#verifier
