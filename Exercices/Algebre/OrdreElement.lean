import Exercices.Algebre.Puissances

/-!
# Puissances et ordre d'un élément

Si `aⁿ = 1`, alors toutes les puissances `a^(n·k)` valent aussi 1. (Le plus petit tel `n > 0` s'appelle
l'**ordre** de `a`.)

## À prouver
1. `un_puiss : (1 : G) ^ k = 1`
2. `puiss_mul : a ^ (m * n) = (a ^ m) ^ n`
3. `puiss_ordre : a ^ n = 1 → a ^ (n * k) = 1`

---
*Exercice* `Algebre.OrdreElement` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Algebre.OrdreElement` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Algebre

variable {G : Type} [Groupe G]

theorem un_puiss (k : Nat) : (1 : G) ^ k = 1 := by
  sorry

theorem puiss_mul (a : G) (m n : Nat) : a ^ (m * n) = (a ^ m) ^ n := by
  sorry

theorem puiss_ordre {a : G} {n : Nat} (h : a ^ n = 1) (k : Nat) : a ^ (n * k) = 1 := by
  sorry

end Parcours.Algebre

#verifier
