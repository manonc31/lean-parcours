/- @parcours
titre: Le paradoxe du chevalier de Méré
difficulte: 1
requiert: Probabilites.Des
indice: Ce sont des calculs : `decide`.
indice: Mais prends le temps de comprendre pourquoi ces inégalités traduisent les probabilités !
-/
import Solutions.Probabilites.Definitions

/-!
# Le paradoxe du chevalier de Méré

En 1654, le chevalier de Méré, joueur, remarque :
- parier sur « au moins un 6 en 4 lancers d'un dé » est **gagnant** à long terme ;
- parier sur « au moins un double 6 en 24 lancers de deux dés » est **perdant**…
alors que son raisonnement (faux) lui disait que c'était pareil. Il pose la question à Pascal, qui en
discute avec Fermat : la théorie des probabilités est née !

- P(aucun 6 en 4 lancers) = `(5/6)⁴ < 1/2`, soit `2 × 5⁴ < 6⁴`.
- P(aucun double 6 en 24 lancers) = `(35/36)²⁴ > 1/2`, soit `36²⁴ < 2 × 35²⁴`.

Et pour finir : une grille de Loto (5 numéros parmi 49, plus un numéro chance parmi 10) a une chance
sur 19 068 840 de gagner.

## À prouver
1. `mere_un_de : 2 * 5 ^ 4 < 6 ^ 4`
2. `mere_deux_des : 36 ^ 24 < 2 * 35 ^ 24`
3. `loto : fact 49 / (fact 5 * fact 44) * 10 = 19068840`
-/

namespace Parcours.Proba

theorem mere_un_de : 2 * 5 ^ 4 < 6 ^ 4 := by -- @exo
  decide

theorem mere_deux_des : 36 ^ 24 < 2 * 35 ^ 24 := by -- @exo
  decide

theorem loto : Parcours.Recurrence.fact 49 / (Parcours.Recurrence.fact 5 * Parcours.Recurrence.fact 44) * 10 = 19068840 := by -- @exo
  decide

end Parcours.Proba

#verifier
