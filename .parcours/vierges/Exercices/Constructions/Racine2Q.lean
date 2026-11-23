import Exercices.Constructions.CorpsQ
import Exercices.Arithmetique.Racine2

/-!
# √2 n'est pas dans ton ℚ

Tu as prouvé (branche Arithmétique) qu'il n'existe pas d'entiers `a, b > 0` avec `a² = 2b²`.
Transporte ce résultat dans **ta** construction des rationnels : aucun `x : Qr` ne vérifie `x² = 2`.
C'est exactement pour ça qu'il faut construire les **réels** !

## À prouver
`racine_deux_pas_rationnelle : ¬∃ x : Qr, x * x = 2`

---
*Exercice* `Constructions.Racine2Q` · difficulté ★★★★☆

💡 Indices : `./parcours indice Constructions.Racine2Q` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Constructions

theorem racine_deux_pas_rationnelle : ¬∃ x : Qr, x * x = 2 := by
  sorry

end Parcours.Constructions

#verifier
