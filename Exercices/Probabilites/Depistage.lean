import Exercices.Probabilites.Definitions

/-!
# Les faux positifs

Une maladie touche 1 % de la population. Un test la détecte dans 99 % des cas, et se trompe
chez 5 % des personnes saines. Ton test est positif : quelle est la probabilité que tu sois malade ?
Pas 99 % … mais **1 sur 6** environ !

## Se le représenter
Sur 10 000 personnes : 100 malades, dont 99 testés positifs ; 9 900 saines, dont 495 positives.
Parmi les 594 positifs, seuls 99 sont malades : `99/594 = 1/6`. (C'est la formule de Bayes.)

Chaque personne est un couple `(malade, positif)`.

## À prouver
`un_sur_six : ProbaEst (population.filter (·.2)) (·.1) 1 6`

## Ressources
- [Théorème de Bayes (Wikipédia)](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_de_Bayes)

---
*Exercice* `Probabilites.Depistage` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Probabilites.Depistage` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Proba

def population : List (Bool × Bool) :=
  List.replicate 99 (true, true) ++ List.replicate 1 (true, false) ++
  List.replicate 495 (false, true) ++ List.replicate 9405 (false, false)

theorem taille : population.length = 10000 := by
  sorry

theorem un_sur_six : ProbaEst (population.filter (·.2)) (·.1) 1 6 := by
  sorry

end Parcours.Proba

#verifier
