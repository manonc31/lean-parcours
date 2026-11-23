import Exercices.Constructions.OperationsQ

/-!
# ℚ est un corps

La grande nouveauté de ℚ : on peut **diviser**. Tout rationnel non nul a un inverse.

🔑 **Récompense** : une fois ℚ construit de tes mains, cet exercice débloque le jeton **`Rat`** :
les rationnels de Lean (`Rat`) et leurs lemmes deviennent purs pour la suite (branche Analyse).

## À prouver
1. `add_comm`, `mul_comm`, `mul_add`
2. `inverse (x : Qr) (hx : x ≠ 0) : ∃ y, x * y = 1`

---
*Exercice* `Constructions.CorpsQ` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Constructions.CorpsQ` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Constructions.Qr

theorem add_comm (x y : Qr) : x + y = y + x := by
  sorry

theorem mul_comm (x y : Qr) : x * y = y * x := by
  sorry

theorem mul_add (x y z : Qr) : x * (y + z) = x * y + x * z := by
  sorry

theorem inverse (x : Qr) (hx : x ≠ 0) : ∃ y, x * y = 1 := by
  sorry

end Parcours.Constructions.Qr

#verifier
