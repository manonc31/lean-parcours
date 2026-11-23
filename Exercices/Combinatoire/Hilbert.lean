import Exercices.Combinatoire.Definitions

/-!
# L'hôtel de Hilbert

Un hôtel a une infinité de chambres numérotées `0, 1, 2, …`, toutes occupées. Arrive un car
infini de cars infinis de touristes : le touriste `b` du car `a`. Peut-on loger tout le monde ?
Oui ! Il y a autant de couples `(a, b)` que d'entiers : on les énumère **par diagonales**.

```
(0,0) → (1,0) → (0,1) → (2,0) → (1,1) → (0,2) → (3,0) → …
  0       1       2       3       4       5       6
```

`code (a, b) = tri (a + b) + b` (avec `tri m = 0 + 1 + ⋯ + m`) et `decode` parcourt les diagonales.

## À prouver
1. `tri_ge : m ≤ tri m`
2. `code_suivant : code (suivant p) = code p + 1`
3. `code_decode : code (decode n) = n`
4. `decode_code : decode (code p) = p`
5. `hilbert : ∃ f : Nat × Nat → Nat, (∀ p q, f p = f q → p = q) ∧ ∀ n, ∃ p, f p = n`

## Ressources
- [Hôtel de Hilbert (Wikipédia)](https://fr.wikipedia.org/wiki/H%C3%B4tel_de_Hilbert)
- [Fonction de couplage (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Pairing_function)

---
*Exercice* `Combinatoire.Hilbert` · difficulté ★★★★☆

💡 Indices : `./parcours indice Combinatoire.Hilbert` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Combi

def tri : Nat → Nat
  | 0 => 0
  | m + 1 => tri m + m + 1

def code (p : Nat × Nat) : Nat := tri (p.1 + p.2) + p.2

def suivant : Nat × Nat → Nat × Nat
  | (0, b) => (b + 1, 0)
  | (a + 1, b) => (a, b + 1)

def decode : Nat → Nat × Nat
  | 0 => (0, 0)
  | n + 1 => suivant (decode n)

theorem tri_ge (m : Nat) : m ≤ tri m := by
  sorry

theorem code_suivant (p : Nat × Nat) : code (suivant p) = code p + 1 := by
  sorry

theorem code_decode (n : Nat) : code (decode n) = n := by
  sorry

theorem decode_code (p : Nat × Nat) : decode (code p) = p := by
  sorry

theorem hilbert : ∃ f : Nat × Nat → Nat, (∀ p q, f p = f q → p = q) ∧ ∀ n, ∃ p, f p = n := by
  sorry

end Parcours.Combi

#verifier
