import ParcoursOutils

/-!
# Implications circulaires

Pour montrer que trois propositions sont équivalentes, il suffit d'un **cycle** d'implications :
`P → Q → R → P`. Technique très utilisée dans les livres de maths (« les assertions suivantes sont équivalentes »).

## À prouver
`circulaire : (P → Q) → (Q → R) → (R → P) → (P ↔ Q) ∧ (Q ↔ R)`

---
*Exercice* `Logique.Circulaire` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Logique.Circulaire` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Logique

theorem circulaire {P Q R : Prop} (h1 : P → Q) (h2 : Q → R) (h3 : R → P) :
    (P ↔ Q) ∧ (Q ↔ R) := by
  sorry

end Parcours.Logique

#verifier
