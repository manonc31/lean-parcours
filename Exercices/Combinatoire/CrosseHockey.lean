import Exercices.Combinatoire.BinomBase

/-!
# La crosse de hockey

Dans le triangle de Pascal, additionne les nombres d'une diagonale, en partant du bord :
`1 + 3 + 6 + 10 = 20`. Le résultat est juste en dessous, décalé d'un cran : la figure dessine une
**crosse de hockey**.

## À prouver
`crosse_hockey : somme (fun i => binom (i + k) k) (m + 1) = binom (m + k + 1) (k + 1)`

## Ressources
- [Identité de la crosse de hockey (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Hockey-stick_identity)

---
*Exercice* `Combinatoire.CrosseHockey` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Combinatoire.CrosseHockey` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Combi

open Parcours.Recurrence

theorem crosse_hockey (k m : Nat) :
    somme (fun i => binom (i + k) k) (m + 1) = binom (m + k + 1) (k + 1) := by
  sorry

end Parcours.Combi

#verifier
