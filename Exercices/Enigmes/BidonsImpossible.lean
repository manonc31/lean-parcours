import Exercices.Enigmes.Bidons

/-!
# Des bidons impossibles

Avec un bidon de 6 litres et un bidon de 9 litres, peut-on obtenir 4 litres ? Non ! Quoi qu'on
fasse, chaque bidon contient toujours un **multiple de 3** litres : c'est un **invariant**.
(En général, on obtient exactement les multiples du PGCD des deux capacités.)

`Accessible A B e` : l'état `e` peut être atteint depuis `(0, 0)`.

## À prouver
1. `invariant : Accessible 6 9 e → e.1 % 3 = 0 ∧ e.2 % 3 = 0`
2. `jamais_quatre : Accessible 6 9 e → e.1 ≠ 4 ∧ e.2 ≠ 4`

---
*Exercice* `Enigmes.BidonsImpossible` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Enigmes.BidonsImpossible` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Enigmes

inductive Accessible (A B : Nat) : Contenu → Prop
  | depart : Accessible A B (0, 0)
  | coup {e e' : Contenu} : Accessible A B e → e' ∈ suivants A B e → Accessible A B e'

theorem invariant (e : Contenu) (h : Accessible 6 9 e) : e.1 % 3 = 0 ∧ e.2 % 3 = 0 := by
  sorry

theorem jamais_quatre (e : Contenu) (h : Accessible 6 9 e) : e.1 ≠ 4 ∧ e.2 ≠ 4 := by
  sorry

end Parcours.Enigmes

#verifier
