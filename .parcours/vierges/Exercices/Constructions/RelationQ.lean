import Exercices.Constructions.Entiers

/-!
# La relation qui définit ℚ

Une fraction est un couple `(a, d)` avec `a : Int`. Pour éviter le dénominateur nul, `(a, d)`
représente `a / (d + 1)` (avec `d : Nat`, donc `d + 1 ≥ 1`).

`a / (b+1) = c / (d+1)`  ⟺  `a × (d+1) = c × (b+1)`  (produit en croix)

À toi de prouver que c'est une relation d'équivalence. La transitivité demande de **simplifier**
par un nombre non nul : c'est ici qu'on a besoin que les dénominateurs ne soient pas nuls !

## À prouver
1. `relQ_refl`, `relQ_symm`, `relQ_trans`

## Ressources
- [Construction des rationnels (Wikipédia)](https://fr.wikipedia.org/wiki/Construction_des_nombres_rationnels)

---
*Exercice* `Constructions.RelationQ` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Constructions.RelationQ` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Constructions

/-- `(a, d)` représente la fraction `a / (d + 1)`. -/
def RelQ (p q : Int × Nat) : Prop := p.1 * ((q.2 : Int) + 1) = q.1 * ((p.2 : Int) + 1)

theorem relQ_refl (p : Int × Nat) : RelQ p p := by
  sorry

theorem relQ_symm {p q : Int × Nat} (h : RelQ p q) : RelQ q p := by
  sorry

theorem relQ_trans {p q r : Int × Nat} (h1 : RelQ p q) (h2 : RelQ q r) : RelQ p r := by
  sorry

end Parcours.Constructions

#verifier
