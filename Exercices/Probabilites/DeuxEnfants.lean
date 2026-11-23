import Exercices.Probabilites.Definitions

/-!
# Le paradoxe des deux enfants

Une famille a deux enfants. On sait qu'**au moins l'un** est un garçon. Quelle est la probabilité
que les **deux** soient des garçons ? Intuition : 1/2. Réponse : **1/3** !

Mais si on sait que **l'aîné** est un garçon, c'est bien 1/2. Toute la subtilité des probabilités
conditionnelles est là.

`true` = garçon. Une famille = (aîné, cadet), 4 issues équiprobables.

## À prouver
1. `au_moins_un : ProbaEst (familles.filter auMoinsUnGarcon) deuxGarcons 1 3`
2. `l_aine : ProbaEst (familles.filter (fun f => f.1)) deuxGarcons 1 2`

## Ressources
- [Paradoxe des deux enfants (Wikipédia)](https://fr.wikipedia.org/wiki/Paradoxe_des_deux_enfants)

---
*Exercice* `Probabilites.DeuxEnfants` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Probabilites.DeuxEnfants` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Proba

def familles : List (Bool × Bool) := [(true, true), (true, false), (false, true), (false, false)]

def auMoinsUnGarcon (f : Bool × Bool) : Bool := f.1 || f.2
def deuxGarcons (f : Bool × Bool) : Bool := f.1 && f.2

theorem au_moins_un : ProbaEst (familles.filter auMoinsUnGarcon) deuxGarcons 1 3 := by
  sorry

theorem l_aine : ProbaEst (familles.filter (fun f => f.1)) deuxGarcons 1 2 := by
  sorry

end Parcours.Proba

#verifier
