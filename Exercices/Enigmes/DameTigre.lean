import Exercices.Logique.Bilan

/-!
# La dame ou le tigre ?

Raymond Smullyan, *La dame ou le tigre ?* (1982) : un prisonnier doit choisir entre deux portes.
Derrière chacune se trouve une dame (qu'il épousera) ou un tigre (qui le mangera). Des pancartes
l'aident… ou le trompent. `true` = dame, `false` = tigre.

**Épreuve 1.** Porte 1 : « Dans cette pièce il y a une dame, et dans l'autre un tigre. »
Porte 2 : « Une des pièces contient une dame, et une des pièces contient un tigre. »
On sait qu'**une** pancarte dit vrai et l'autre faux.

**Épreuve 2.** Porte 1 : « Au moins une des pièces contient une dame. »
Porte 2 : « Il y a un tigre dans l'autre pièce. » Les deux pancartes disent toutes deux vrai, ou
toutes deux faux.

**Épreuve 3.** Porte 1 : « Il y a un tigre dans cette pièce, ou une dame dans l'autre. »
Porte 2 : « Il y a une dame dans l'autre pièce. » Toutes deux vraies ou toutes deux fausses.

## À prouver
Pour chaque épreuve, la seule possibilité.

## Ressources
- [Raymond Smullyan (Wikipédia)](https://fr.wikipedia.org/wiki/Raymond_Smullyan)

---
*Exercice* `Enigmes.DameTigre` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Enigmes.DameTigre` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Enigmes

theorem epreuve1 (d1 d2 : Bool)
    (h : (d1 && !d2) != ((d1 || d2) && (!d1 || !d2))) : d1 = false ∧ d2 = true := by
  sorry

theorem epreuve2 (d1 d2 : Bool) (h : (d1 || d2) = !d1) : d1 = false ∧ d2 = true := by
  sorry

theorem epreuve3 (d1 d2 : Bool) (h : (!d1 || d2) = d1) : d1 = true ∧ d2 = true := by
  sorry

end Parcours.Enigmes

#verifier
