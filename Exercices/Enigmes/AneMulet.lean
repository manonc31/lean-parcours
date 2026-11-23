import Exercices.Recurrence.Definitions

/-!
# L'âne et le mulet

Une énigme attribuée à Euclide : un âne et un mulet portent des sacs. L'âne se plaint de sa
charge. Le mulet lui dit : « Si tu me donnais un de tes sacs, j'en porterais deux fois plus que
toi ; si je t'en donnais un des miens, nous en porterions autant. » Combien portent-ils ?

## À prouver
`ane_mulet : m + 1 = 2 * (a - 1) → m - 1 = a + 1 → a = 5 ∧ m = 7`

---
*Exercice* `Enigmes.AneMulet` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Enigmes.AneMulet` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Enigmes

theorem ane_mulet (a m : Nat) (h1 : m + 1 = 2 * (a - 1)) (h2 : m - 1 = a + 1) :
    a = 5 ∧ m = 7 := by
  sorry

end Parcours.Enigmes

#verifier
