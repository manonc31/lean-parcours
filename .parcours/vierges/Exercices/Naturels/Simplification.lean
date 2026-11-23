import Exercices.Naturels.AddComm

/-!
# Simplifier une somme

Si `a + c = b + c`, alors `a = b`. Évident ? Il faut pourtant le prouver !
On utilisera l'injectivité du successeur : `succ_inj : succ a = succ b → a = b`.

## À prouver
1. `add_right_cancel (a b c : ℕ) : a + c = b + c → a = b`
2. `add_left_cancel (a b c : ℕ) : a + b = a + c → b = c`

---
*Exercice* `Naturels.Simplification` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Naturels.Simplification` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

theorem add_right_cancel (a b c : ℕ) : a + c = b + c → a = b := by
  sorry

theorem add_left_cancel (a b c : ℕ) : a + b = a + c → b = c := by
  sorry

end Parcours.ℕ

#verifier
