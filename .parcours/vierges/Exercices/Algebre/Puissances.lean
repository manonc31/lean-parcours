import Exercices.Algebre.Inverses

/-!
# Puissances dans un groupe

`a ^ 0 = 1`, `a ^ (n + 1) = a ^ n * a`.

## À prouver
1. `puiss_add : a ^ (m + n) = a ^ m * a ^ n`
2. `puiss_comm : a ^ n * a = a * a ^ n`
3. `puiss_inv : (a⁻¹) ^ n = (a ^ n)⁻¹`

---
*Exercice* `Algebre.Puissances` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Algebre.Puissances` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Algebre

variable {G : Type} [Groupe G]

def puiss (a : G) : Nat → G
  | 0 => 1
  | n + 1 => puiss a n * a

instance instPuiss : HPow G Nat G := ⟨puiss⟩

theorem puiss_zero (a : G) : a ^ 0 = 1 := rfl
theorem puiss_succ (a : G) (n : Nat) : a ^ (n + 1) = a ^ n * a := rfl

theorem puiss_add (a : G) (m n : Nat) : a ^ (m + n) = a ^ m * a ^ n := by
  sorry

theorem puiss_comm (a : G) (n : Nat) : a ^ n * a = a * a ^ n := by
  sorry

theorem puiss_inv (a : G) (n : Nat) : (a⁻¹) ^ n = (a ^ n)⁻¹ := by
  sorry

end Parcours.Algebre

#verifier
