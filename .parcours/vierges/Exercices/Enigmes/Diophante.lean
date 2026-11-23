import Exercices.Recurrence.Definitions

/-!
# L'épitaphe de Diophante

« Passant, sous ce tombeau repose Diophante. Ces quelques vers vont te dire la durée de sa vie.
Son enfance en a occupé la sixième partie ; puis sa barbe a poussé pendant un douzième ; il se maria
après un septième, et cinq ans plus tard il eut un fils. Mais ce fils mourut à la moitié de l'âge
qu'atteignit son père, qui lui survécut quatre ans. »

En notant `x` l'âge de Diophante (multiple de 84 pour que toutes les fractions soient entières) :
`x/6 + x/12 + x/7 + 5 + x/2 + 4 = x`.

## À prouver
`diophante (h84 : x % 84 = 0) (h : x / 6 + x / 12 + x / 7 + 5 + x / 2 + 4 = x) : x = 84`

---
*Exercice* `Enigmes.Diophante` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Enigmes.Diophante` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Enigmes

theorem diophante (x : Nat) (h84 : x % 84 = 0) (h : x / 6 + x / 12 + x / 7 + 5 + x / 2 + 4 = x) :
    x = 84 := by
  sorry

end Parcours.Enigmes

#verifier
