import Exercices.Probabilites.Definitions

/-!
# Le paradoxe de Simpson

Une étude médicale (1986) compare deux traitements des calculs rénaux :

| | petits calculs | gros calculs | total |
|---|---|---|---|
| Traitement A | 81/87 guéris | 192/263 | 273/350 |
| Traitement B | 234/270 | 55/80 | 289/350 |

A fait **mieux** que B pour les petits calculs, **mieux** pour les gros… mais **moins bien** au
total ! Explication : A a surtout été donné pour les cas difficiles (gros calculs). Méfiance avec
les moyennes !

`meilleur a b c d` signifie `a/b > c/d` (produit en croix).

## À prouver
`petits`, `gros`, `total_simpson`.

## Ressources
- [Paradoxe de Simpson (Wikipédia)](https://fr.wikipedia.org/wiki/Paradoxe_de_Simpson)

---
*Exercice* `Probabilites.Simpson` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Probabilites.Simpson` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Proba

abbrev meilleur (a b c d : Nat) : Prop := c * b < a * d

theorem petits : meilleur 81 87 234 270 := by
  sorry

theorem gros : meilleur 192 263 55 80 := by
  sorry

theorem total_simpson : meilleur 289 350 273 350 := by
  sorry

end Parcours.Proba

#verifier
