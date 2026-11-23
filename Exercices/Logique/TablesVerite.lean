import ParcoursOutils

/-!
# Tables de vérité

En Lean il y a deux mondes : les **propositions** (`Prop`, ce qu'on prouve) et les **booléens**
(`Bool`, ce qu'on calcule). `&&`, `||`, `!` sont les versions calculables de `∧`, `∨`, `¬`.
Comme un booléen n'a que deux valeurs, une égalité de booléens se vérifie en essayant tous les cas :
c'est la méthode des **tables de vérité**.

## À prouver
1. `de_morgan_bool : !(a && b) = (!a || !b)`
2. `distrib_bool : (a && (b || c)) = ((a && b) || (a && c))`
3. `et_vrai_iff : (a && b) = true ↔ a = true ∧ b = true`

---
*Exercice* `Logique.TablesVerite` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Logique.TablesVerite` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Logique

theorem de_morgan_bool (a b : Bool) : (!(a && b)) = (!a || !b) := by
  sorry

theorem distrib_bool (a b c : Bool) : (a && (b || c)) = ((a && b) || (a && c)) := by
  sorry

theorem et_vrai_iff (a b : Bool) : (a && b) = true ↔ a = true ∧ b = true := by
  sorry

end Parcours.Logique

#verifier
