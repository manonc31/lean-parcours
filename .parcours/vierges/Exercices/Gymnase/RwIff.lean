import ParcoursOutils

/-!
# Réécrire avec une équivalence

`rw` marche aussi avec `h : P ↔ Q` : il remplace la **proposition** `P` par `Q` dans le but.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.RwIff` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Gymnase.RwIff` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem rw_iff (P Q : Prop) (h : P ↔ Q) (hq : Q) : P := by
  sorry

end Parcours.Gymnase

#verifier
