/- @parcours
titre: Le pont vers les entiers de Lean
difficulte: 3
genre: pont
debloque: Nat
requiert: Naturels.MulComm, Naturels.LeTotal, Naturels.Strict
indice: `toNat_ofNat` : récurrence sur `n` (un `Nat` de Lean : cas `zero` et `succ n ih`, le but du second est `toNat (ofNat (n + 1)) = n + 1`). Utilise `show toNat (ofNat n) + 1 = n + 1`, puis `rw [ih]`.
indice: `ofNat_toNat` : récurrence sur `a`, avec `show succ (ofNat (toNat a)) = succ a`.
indice: `toNat_injective` : `rw [← ofNat_toNat a, h, ofNat_toNat]`.
indice: `toNat_add` : récurrence sur `b` ; dans le cas `succ`, `show toNat (a + b) + 1 = toNat a + (toNat b + 1)`, puis `rw [ih]` (et `rfl` si besoin : pour le `Nat` de Lean, `x + (y + 1)` et `(x + y) + 1` sont égaux par définition).
indice: `toNat_mul` : récurrence sur `b` ; cas `succ` : `show toNat (a * b + a) = toNat a * (toNat b + 1)`, puis `rw [toNat_add, ih]` et `rfl`.
-/
import Solutions.Naturels.Multiplication

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
-/

namespace Parcours.ℕ

theorem toNat_ofNat (n : Nat) : toNat (ofNat n) = n := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    show toNat (ofNat n) + 1 = n + 1
    rw [ih]

theorem ofNat_toNat (a : ℕ) : ofNat (toNat a) = a := by -- @exo
  induction a with
  | zero => rfl
  | succ a ih =>
    show succ (ofNat (toNat a)) = succ a
    rw [ih]

theorem toNat_injective (a b : ℕ) (h : toNat a = toNat b) : a = b := by -- @exo
  rw [← ofNat_toNat a, h, ofNat_toNat]

theorem toNat_add (a b : ℕ) : toNat (a + b) = toNat a + toNat b := by -- @exo
  induction b with
  | zero => rfl
  | succ b ih =>
    show toNat (a + b) + 1 = toNat a + (toNat b + 1)
    rw [ih]
    rfl

theorem toNat_mul (a b : ℕ) : toNat (a * b) = toNat a * toNat b := by -- @exo
  induction b with
  | zero => rfl
  | succ b ih =>
    show toNat (a * b + a) = toNat a * (toNat b + 1)
    rw [toNat_add, ih]
    rfl

end Parcours.ℕ

#verifier
