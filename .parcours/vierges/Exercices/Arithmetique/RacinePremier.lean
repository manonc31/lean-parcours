import Exercices.Arithmetique.LemmeEuclide

/-!
# √p est irrationnel

Généralisation : pour tout nombre premier `p`, `√p` est irrationnel.

## À prouver
`racine_premier_irrationnelle (hp : Premier p) : ¬∃ a b : Nat, 0 < b ∧ a * a = p * (b * b)`

---
*Exercice* `Arithmetique.RacinePremier` · difficulté ★★★★☆

💡 Indices : `./parcours indice Arithmetique.RacinePremier` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Arith

theorem racine_premier_irrationnelle {p : Nat} (hp : Premier p) :
    ¬∃ a b : Nat, 0 < b ∧ a * a = p * (b * b) := by
  sorry

end Parcours.Arith

#verifier
