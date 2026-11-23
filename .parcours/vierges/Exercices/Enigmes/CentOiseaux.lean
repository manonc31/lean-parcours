import Exercices.Recurrence.Definitions

/-!
# Les cent volailles

Un problème chinois du Vᵉ siècle (Zhang Qiujian) : un coq coûte 5 sapèques, une poule 3, et
on a 3 poussins pour 1 sapèque. Avec 100 sapèques, on achète exactement 100 volailles. Combien de
chaque ? Il y a **quatre** solutions !

En multipliant le prix par 3 pour éviter les fractions : `15c + 9p + q = 300`.

## À prouver
`cent_oiseaux` : les quatre solutions, et seulement elles.

---
*Exercice* `Enigmes.CentOiseaux` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Enigmes.CentOiseaux` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Enigmes

def Achat (c p q : Nat) : Prop := c + p + q = 100 ∧ 15 * c + 9 * p + q = 300

theorem cent_oiseaux (c p q : Nat) : Achat c p q ↔
    (c = 0 ∧ p = 25 ∧ q = 75) ∨ (c = 4 ∧ p = 18 ∧ q = 78) ∨
    (c = 8 ∧ p = 11 ∧ q = 81) ∨ (c = 12 ∧ p = 4 ∧ q = 84) := by
  sorry

end Parcours.Enigmes

#verifier
