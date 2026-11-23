import Exercices.Listes.Pont
import Exercices.Recurrence.Definitions

/-!
# Le calendrier perpétuel

La **congruence de Zeller** donne le jour de la semaine de n'importe quelle date (calendrier
grégorien) : `0` = samedi, `1` = dimanche, `2` = lundi, `3` = mardi… Janvier et février comptent
comme les mois 13 et 14 de l'année précédente (pour que le 29 février soit à la fin).

## À prouver
1. `bastille` : le 14 juillet 1789 était un mardi.
2. `an_2000` : le 1ᵉʳ janvier 2000 était un samedi.
3. `periode : zeller j m (a + 400) = zeller j m a` : le calendrier se répète tous les 400 ans.

## Ressources
- [Congruence de Zeller (Wikipédia)](https://fr.wikipedia.org/wiki/Congruence_de_Zeller)

---
*Exercice* `Enigmes.Calendrier` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Enigmes.Calendrier` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Enigmes

def zeller (jour mois annee : Nat) : Nat :=
  let m := if mois ≤ 2 then mois + 12 else mois
  let a := if mois ≤ 2 then annee - 1 else annee
  (jour + 13 * (m + 1) / 5 + a % 100 + a % 100 / 4 + a / 100 / 4 + 5 * (a / 100)) % 7

theorem bastille : zeller 14 7 1789 = 3 := by
  sorry

theorem an_2000 : zeller 1 1 2000 = 0 := by
  sorry

theorem periode (j m a : Nat) (ha : 1 ≤ a) : zeller j m (a + 400) = zeller j m a := by
  sorry

end Parcours.Enigmes

#verifier
