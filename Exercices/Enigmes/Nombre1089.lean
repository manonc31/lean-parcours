import Exercices.Recurrence.Definitions

/-!
# Le tour du 1089

Un tour de magie : pense à un nombre de 3 chiffres dont le premier chiffre est plus grand que le
dernier (par exemple 732). Retourne-le (237) et soustrais : `732 − 237 = 495`. Retourne le
résultat (594) et ajoute : `495 + 594 = 1089`. Quel que soit ton nombre, tu trouves **1089** !

(Les nombres comme 99 s'écrivent 099 sur trois chiffres.)

## À prouver
`tour_1089 : n < 1000 → n % 10 < n / 100 → tour1089 n = 1089`

---
*Exercice* `Enigmes.Nombre1089` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Enigmes.Nombre1089` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Enigmes

def renverser3 (n : Nat) : Nat := (n % 10) * 100 + (n / 10 % 10) * 10 + n / 100

def tour1089 (n : Nat) : Nat := (n - renverser3 n) + renverser3 (n - renverser3 n)

theorem tour_1089 : ∀ n, n < 1000 → n % 10 < n / 100 → tour1089 n = 1089 := by
  sorry

end Parcours.Enigmes

#verifier
