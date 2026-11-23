import Exercices.Analyse.Cauchy

/-!
# 💀 ℚ n'est pas complet

Il existe une suite de rationnels qui est de Cauchy (ses termes se resserrent indéfiniment) mais
qui ne converge vers **aucun** rationnel : elle « converge vers un trou » de ℚ, comme `√2`.
C'est la raison d'être des nombres réels (et des coupures de Dedekind que tu as construites).

Boss sans solution de référence.

## À prouver
`q_pas_complet : ∃ u : Suite, Cauchy u ∧ ¬∃ l, Tend u l`

---
*Exercice* `Analyse.QPasComplet` · difficulté ★★★★★

💡 Indices : `./parcours indice Analyse.QPasComplet` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Analyse

theorem q_pas_complet : ∃ u : Suite, Cauchy u ∧ ¬∃ l, Tend u l := by
  sorry

end Parcours.Analyse

#verifier
