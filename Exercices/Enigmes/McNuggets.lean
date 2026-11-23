import Exercices.Recurrence.Definitions

/-!
# Le théorème des McNuggets

Les McNuggets étaient vendus par boîtes de 6, 9 et 20. Quel est le plus grand nombre de nuggets
qu'on ne peut **pas** commander exactement ? Réponse : **43**. Tout nombre à partir de 44 est
possible.

## Se le représenter
Si on sait faire 44, 45, 46, 47, 48 et 49 (six nombres consécutifs), on sait faire tous les
suivants en ajoutant des boîtes de 6.

## À prouver
1. `pas_43 : ¬ Commande 43`
2. `a_partir_de_44 : 44 ≤ n → Commande n`

## Ressources
- [Nombre de McNugget (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Coin_problem#McNugget_numbers)

---
*Exercice* `Enigmes.McNuggets` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Enigmes.McNuggets` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Enigmes

def Commande (n : Nat) : Prop := ∃ a b c, n = 6 * a + 9 * b + 20 * c

theorem pas_43 : ¬ Commande 43 := by
  sorry

theorem a_partir_de_44 : ∀ n, 44 ≤ n → Commande n := by
  sorry

end Parcours.Enigmes

#verifier
