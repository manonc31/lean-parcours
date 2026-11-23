import Exercices.Algebre.Inverses

/-!
# Sous-groupes

Un **sous-groupe** de `G` est une partie qui contient `1`, et qui est stable par `*` et `⁻¹`.

## À faire
1. `inter H K` : l'intersection de deux sous-groupes est un sous-groupe.
2. `centre G` : les éléments qui commutent avec tout le monde forment un sous-groupe.

---
*Exercice* `Algebre.SousGroupes` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Algebre.SousGroupes` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Algebre

variable {G : Type} [Groupe G]

structure SousGroupe (G : Type) [Groupe G] where
  mem : G → Prop
  one_mem : mem 1
  mul_mem : ∀ {a b}, mem a → mem b → mem (a * b)
  inv_mem : ∀ {a}, mem a → mem a⁻¹

def SousGroupe.inter (H K : SousGroupe G) : SousGroupe G :=
  sorry

def centre (G : Type) [Groupe G] : SousGroupe G :=
  sorry

end Parcours.Algebre

#verifier
