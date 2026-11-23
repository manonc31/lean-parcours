import Exercices.Programmes.Definitions

/-!
# Additionner avec un accumulateur

Un programme qui additionne une liste « comme à la main » : on garde un total partiel `acc`
(l'**accumulateur**) et on lui ajoute les éléments un par un. C'est ce que fait une boucle `for`.

Le piège : pour la récurrence, il faut que l'énoncé parle de **n'importe quel** accumulateur de
départ, pas seulement de `0`.

## À prouver
1. `sommeAcc_spec : sommeAcc l acc = acc + l.sum`
2. `sommeAcc_zero : sommeAcc l 0 = l.sum`

---
*Exercice* `Programmes.Accumulateur` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Programmes.Accumulateur` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

def sommeAcc : List Nat → Nat → Nat
  | [], acc => acc
  | x :: l, acc => sommeAcc l (acc + x)

theorem sommeAcc_spec (l : List Nat) (acc : Nat) : sommeAcc l acc = acc + l.sum := by
  sorry

theorem sommeAcc_zero (l : List Nat) : sommeAcc l 0 = l.sum := by
  sorry

end Parcours.Prog

#verifier
