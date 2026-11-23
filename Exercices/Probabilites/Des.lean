import Exercices.Probabilites.Definitions

/-!
# Lancer deux dés

On lance deux dés équilibrés. Quelle est la probabilité…
- que la somme fasse 7 ? (la somme la plus fréquente !)
- de faire un double ?
- que la somme soit au moins 10 ?
- que le premier dé soit pair ET la somme fasse 7 ? Est-ce égal au produit des probabilités
  (événements **indépendants**) ?

## À prouver
1. `somme_sept : ProbaEst deuxDes (fun p => p.1 + p.2 == 7) 1 6`
2. `double : ProbaEst deuxDes (fun p => p.1 == p.2) 1 6`
3. `au_moins_dix : ProbaEst deuxDes (fun p => 10 ≤ p.1 + p.2) 1 6`
4. `independance` : P(premier pair et somme 7) = 1/12 = 1/2 × 1/6

---
*Exercice* `Probabilites.Des` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Probabilites.Des` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Proba

theorem somme_sept : ProbaEst deuxDes (fun p => p.1 + p.2 == 7) 1 6 := by
  sorry

theorem double : ProbaEst deuxDes (fun p => p.1 == p.2) 1 6 := by
  sorry

theorem au_moins_dix : ProbaEst deuxDes (fun p => decide (10 ≤ p.1 + p.2)) 1 6 := by
  sorry

theorem independance : ProbaEst deuxDes (fun p => p.1 % 2 == 0) 1 2 ∧
    ProbaEst deuxDes (fun p => p.1 % 2 == 0 && p.1 + p.2 == 7) 1 12 := by
  sorry

end Parcours.Proba

#verifier
