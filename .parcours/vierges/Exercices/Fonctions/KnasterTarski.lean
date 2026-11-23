import Exercices.Fonctions.Ensembles

/-!
# Le théorème du point fixe de Knaster–Tarski

Soit `F : Ens α → Ens α` **croissante** : si `s ⊆ t` alors `F s ⊆ F t`.
Alors `F` a un **point fixe** : un ensemble `s` tel que `F s = s`.

Ce théorème (1928/1955) est partout en informatique : sémantique des boucles, définitions
inductives, analyse de programmes… et il donne une preuve élégante de Cantor–Schröder–Bernstein.

## À prouver
`knaster_tarski (F : Ens α → Ens α) (hF : ∀ s t, s ⊆ t → F s ⊆ F t) : ∃ s, F s = s`

## Ressources
- [Théorème de Knaster-Tarski (Wikipédia)](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_de_Knaster-Tarski)

---
*Exercice* `Fonctions.KnasterTarski` · difficulté ★★★★☆

💡 Indices : `./parcours indice Fonctions.KnasterTarski` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Fonctions

theorem knaster_tarski {α : Type} (F : Ens α → Ens α) (hF : ∀ s t, s ⊆ t → F s ⊆ F t) :
    ∃ s, F s = s := by
  sorry

end Parcours.Fonctions

#verifier
