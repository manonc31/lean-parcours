import ParcoursOutils

/-!
# Étapes intermédiaires avec have

`have hq : Q := hpq hp` ajoute un nouveau fait à tes hypothèses. Pratique pour découper une preuve.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.Have` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Gymnase.Have` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem have_exemple (P Q R : Prop) (hp : P) (hpq : P → Q) (hqr : Q → R) : R := by
  sorry

end Parcours.Gymnase

#verifier
