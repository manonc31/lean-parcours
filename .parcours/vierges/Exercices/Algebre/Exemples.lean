import Exercices.Algebre.Exposant2
import Exercices.Naturels.Transfert

/-!
# Des exemples de groupes

Construis deux groupes concrets en donnant leurs opérations et en prouvant les axiomes :
1. `Bool` avec le « ou exclusif » (`xor`), neutre `false`, et chaque élément son propre inverse.
2. Les entiers relatifs `Int` avec l'**addition** (on l'enveloppe dans une structure `Additif`
   pour pouvoir noter l'addition `*`).

Puis profite : tous tes théorèmes s'appliquent automatiquement.

## À faire
1. `instance groupeBool : Groupe Bool`
2. `instance groupeAdditif : Groupe Additif`
3. `bool_commutatif : ∀ a b : Bool, a * b = b * a` (sans calcul : utilise ton théorème sur `x * x = 1` !)

---
*Exercice* `Algebre.Exemples` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Algebre.Exemples` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Algebre

instance groupeBool : Groupe Bool :=
  sorry

/-- Les entiers relatifs, vus avec l'addition. -/
structure Additif where
  val : Int

instance groupeAdditif : Groupe Additif :=
  sorry

theorem bool_commutatif (a b : Bool) : a * b = b * a := by
  sorry

end Parcours.Algebre

#verifier
