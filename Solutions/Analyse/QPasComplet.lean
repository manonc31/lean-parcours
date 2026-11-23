/- @parcours
titre: ℚ n'est pas complet
difficulte: 5
genre: boss
solution: non
requiert: Analyse.Cauchy, Analyse.Bornee, Constructions.Racine2Q
indice: Prends une suite qui « veut » tendre vers √2, par exemple la méthode de Héron : `u 0 = 2`, `u (n+1) = (u n + 2 / u n) / 2`.
indice: Montre qu'elle est de Cauchy : `0 ≤ u n - √2`… sans parler de √2 ! Travaille avec `u n ^ 2 - 2`, qui est divisé (au moins) par 2 à chaque étape.
indice: Si elle convergeait vers `l : Rat`, alors `l² = 2` (passe à la limite dans la récurrence). Contradiction avec l'irrationalité de √2 (tu l'as prouvée dans plusieurs branches).
-/
import Solutions.Analyse.Cauchy

/-!
# 💀 ℚ n'est pas complet

Il existe une suite de rationnels qui est de Cauchy (ses termes se resserrent indéfiniment) mais
qui ne converge vers **aucun** rationnel : elle « converge vers un trou » de ℚ, comme `√2`.
C'est la raison d'être des nombres réels (et des coupures de Dedekind que tu as construites).

Boss sans solution de référence.

## À prouver
`q_pas_complet : ∃ u : Suite, Cauchy u ∧ ¬∃ l, Tend u l`
-/

namespace Parcours.Analyse

theorem q_pas_complet : ∃ u : Suite, Cauchy u ∧ ¬∃ l, Tend u l := by -- @exo
  sorry

end Parcours.Analyse

#verifier
