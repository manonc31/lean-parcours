import ParcoursOutils

/-!
# Enchaîner les tactiques

`t1 <;> t2` applique `t2` à **tous** les buts créés par `t1`. Pratique quand plusieurs cas se prouvent de la même façon.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.Tactiques` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Gymnase.Tactiques` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem enchainer (P Q : Prop) (hp : P) (hq : Q) : (P ∧ Q) ∧ (Q ∧ P) := by
  sorry

end Parcours.Gymnase

#verifier
