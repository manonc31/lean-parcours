import Exercices.Arithmetique.Definitions

/-!
# 💀 IMO 1988, problème 6

> Soient `a` et `b` des entiers strictement positifs tels que `ab + 1` divise `a² + b²`.
> Montrer que `(a² + b²) / (ab + 1)` est un carré parfait.

Le problème le plus célèbre de l'histoire des Olympiades : aucun membre du jury australien qui l'a
proposé ne savait le résoudre, ni les meilleurs théoriciens des nombres du pays. 11 élèves l'ont
résolu pendant l'épreuve. Un des leurs a reçu un prix spécial pour sa solution.

Boss sans solution de référence.

## À prouver
`imo1988 (ha : 0 < a) (hb : 0 < b) (h : (a * b + 1) ∣ (a ^ 2 + b ^ 2)) : ∃ k, (a ^ 2 + b ^ 2) / (a * b + 1) = k ^ 2`

## Ressources
- [Vieta jumping (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Vieta_jumping)

---
*Exercice* `Olympiades.IMO1988` · difficulté ★★★★★

💡 Indices : `./parcours indice Olympiades.IMO1988` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Olymp

theorem imo1988 (a b : Nat) (ha : 0 < a) (hb : 0 < b) (h : (a * b + 1) ∣ (a ^ 2 + b ^ 2)) :
    ∃ k, (a ^ 2 + b ^ 2) / (a * b + 1) = k ^ 2 := by
  sorry

end Parcours.Olymp

#verifier
