import Exercices.Probabilites.PileOuFace

/-!
# Le problème des partis

En 1654, le chevalier de Méré pose à Pascal ce problème : deux joueurs misent 32 pistoles
chacun ; le premier à gagner 3 manches (à pile ou face) emporte tout. La partie est interrompue
alors qu'Alice mène 2 à 1. Comment partager équitablement les 64 pistoles ?

Idée de Fermat : imaginer qu'on joue **toujours** 2 manches de plus (même si la partie est finie
avant) ; Alice gagne si elle remporte au moins une des deux : probabilité 3/4. Elle doit donc
recevoir 48 pistoles, Bob 16. La correspondance entre Pascal et Fermat sur ce problème est
considérée comme l'acte de naissance du calcul des probabilités.

## À prouver
1. `partage : ProbaEst (mots 2) (fun w => w.any id) 3 4`
2. `partage_2_3` : s'il manque 2 manches à Alice et 3 à Bob, on joue 4 manches fictives, et Alice
   gagne avec probabilité 11/16.

## Ressources
- [Problème des partis (Wikipédia)](https://fr.wikipedia.org/wiki/Probl%C3%A8me_des_partis)

---
*Exercice* `Probabilites.Partis` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Probabilites.Partis` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Proba

theorem partage : ProbaEst (mots 2) (fun w => w.any id) 3 4 := by
  sorry

theorem partage_2_3 : ProbaEst (mots 4) (fun w => decide (2 ≤ w.count true)) 11 16 := by
  sorry

end Parcours.Proba

#verifier
