/- @parcours
titre: Implications circulaires
difficulte: 2
requiert: Logique.Equivalence
indice: Chaque sens d'équivalence s'obtient en composant les implications.
indice: `exact ⟨⟨h1, fun q => h3 (h2 q)⟩, ⟨h2, fun r => …⟩⟩`.
-/
import ParcoursOutils

/-!
# Implications circulaires

Pour montrer que trois propositions sont équivalentes, il suffit d'un **cycle** d'implications :
`P → Q → R → P`. Technique très utilisée dans les livres de maths (« les assertions suivantes sont équivalentes »).

## À prouver
`circulaire : (P → Q) → (Q → R) → (R → P) → (P ↔ Q) ∧ (Q ↔ R)`
-/

namespace Parcours.Logique

theorem circulaire {P Q R : Prop} (h1 : P → Q) (h2 : Q → R) (h3 : R → P) :
    (P ↔ Q) ∧ (Q ↔ R) := by -- @exo
  exact ⟨⟨h1, fun q => h3 (h2 q)⟩, ⟨h2, fun r => h1 (h3 r)⟩⟩

end Parcours.Logique

#verifier
