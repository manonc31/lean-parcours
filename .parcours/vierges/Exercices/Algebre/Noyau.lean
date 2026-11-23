import Exercices.Algebre.Morphismes
import Exercices.Algebre.SousGroupes

/-!
# Le noyau d'un morphisme

Le **noyau** de `f` : les `a` tels que `f a = 1`. C'est un sous-groupe, et il mesure exactement
le défaut d'injectivité : `f` est injectif si et seulement si son noyau est `{1}`.

## À faire
1. `Morphisme.noyau : SousGroupe G`
2. `injectif_iff_noyau : (∀ a b, f a = f b → a = b) ↔ (∀ a, f a = 1 → a = 1)`

---
*Exercice* `Algebre.Noyau` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Algebre.Noyau` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Algebre

variable {G H : Type} [Groupe G] [Groupe H]

def Morphisme.noyau (φ : Morphisme G H) : SousGroupe G :=
  sorry

theorem injectif_iff_noyau (φ : Morphisme G H) :
    (∀ a b, φ.f a = φ.f b → a = b) ↔ (∀ a, φ.f a = 1 → a = 1) := by
  sorry

end Parcours.Algebre

#verifier
