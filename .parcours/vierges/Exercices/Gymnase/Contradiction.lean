import ParcoursOutils

/-!
# Repérer une contradiction

Avec `hp : P` et `hnp : ¬P`, la tactique `contradiction` conclut toute seule. Elle repère aussi les égalités impossibles entre constructeurs, comme `0 = n + 1`.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.Contradiction` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Gymnase.Contradiction` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem contradiction_exemple (P Q : Prop) (hp : P) (hnp : ¬P) : Q := by
  sorry

theorem pas_de_predecesseur (n : Nat) (h : n + 1 = 0) : False := by
  sorry

end Parcours.Gymnase

#verifier
