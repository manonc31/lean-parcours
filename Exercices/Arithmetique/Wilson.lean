import Exercices.Arithmetique.LemmeEuclide

/-!
# 💀 Le théorème de Wilson

> `p` est premier si et seulement si `(p-1)! ≡ -1 (mod p)`.

On demande le sens direct : pour `p` premier, `p` divise `(p-1)! + 1`.
Énoncé par Wilson en 1770, prouvé par Lagrange en 1771.

C'est un **boss** : pas de solution de référence. L'arithmétique est facile sur papier, mais
formaliser le regroupement par paires « élément × inverse » demande de l'organisation.

## À prouver
`wilson (hp : Premier p) : p ∣ Parcours.Recurrence.fact (p - 1) + 1`

## Ressources
- [Théorème de Wilson (Wikipédia)](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_de_Wilson)

---
*Exercice* `Arithmetique.Wilson` · difficulté ★★★★★

💡 Indices : `./parcours indice Arithmetique.Wilson` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Arith

theorem wilson {p : Nat} (hp : Premier p) : p ∣ Parcours.Recurrence.fact (p - 1) + 1 := by
  sorry

end Parcours.Arith

#verifier
