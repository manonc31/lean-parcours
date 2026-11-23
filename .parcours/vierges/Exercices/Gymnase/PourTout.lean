import ParcoursOutils

/-!
# Utiliser un « pour tout »

`h : ∀ n, P n` s'applique à n'importe quel `n` : `h 5 : P 5`. Variante : `specialize h 5` remplace `h` par `h 5`.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.PourTout` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Gymnase.PourTout` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem pour_tout_exemple (P : Nat → Prop) (h : ∀ n, P n) : P 5 := by
  sorry

theorem pour_tout_intro : ∀ n : Nat, n = n := by
  sorry

end Parcours.Gymnase

#verifier
