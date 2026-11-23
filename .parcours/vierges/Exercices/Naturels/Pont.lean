import Exercices.Naturels.Multiplication

/-!
# 🌉 Le pont vers les entiers de Lean

Tu as reconstruit ℕ, `+`, `×` et toutes leurs propriétés. Le `Nat` de Lean est **le même objet** :
prouve-le ! On a deux traductions `toNat : ℕ → Nat` et `ofNat : Nat → ℕ` (définies dans le cours).
Montre qu'elles sont réciproques l'une de l'autre, et que `toNat` respecte `+` et `×`.
(En langage mathématique : `toNat` est un **isomorphisme** de semi-anneaux.)

🔑 **Récompense** : ce pont débloque le jeton **`Nat`** pour tous les exercices qui en dépendent :
les milliers de lemmes de `Nat` de la bibliothèque et la tactique **`omega`** (qui résout
toute seule l'arithmétique linéaire) deviennent autorisés, sans perdre l'étoile ⭐.
C'est la réponse à la question « quand j'ai tout recodé, ai-je le droit d'utiliser le vrai ? » : oui !

Le `Nat` de Lean s'utilise comme le tien, avec `0` et `n + 1` au lieu de `succ n`.

## À prouver
1. `toNat_ofNat (n : Nat) : toNat (ofNat n) = n`
2. `ofNat_toNat (a : ℕ) : ofNat (toNat a) = a`
3. `toNat_injective (a b : ℕ) : toNat a = toNat b → a = b`
4. `toNat_add (a b : ℕ) : toNat (a + b) = toNat a + toNat b`
5. `toNat_mul (a b : ℕ) : toNat (a * b) = toNat a * toNat b`

## Ressources
- [Isomorphisme (Wikipédia)](https://fr.wikipedia.org/wiki/Isomorphisme)

---
*Exercice* `Naturels.Pont` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Naturels.Pont` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

theorem toNat_ofNat (n : Nat) : toNat (ofNat n) = n := by
  sorry

theorem ofNat_toNat (a : ℕ) : ofNat (toNat a) = a := by
  sorry

theorem toNat_injective (a b : ℕ) (h : toNat a = toNat b) : a = b := by
  sorry

theorem toNat_add (a b : ℕ) : toNat (a + b) = toNat a + toNat b := by
  sorry

theorem toNat_mul (a b : ℕ) : toNat (a * b) = toNat a * toNat b := by
  sorry

end Parcours.ℕ

#verifier
