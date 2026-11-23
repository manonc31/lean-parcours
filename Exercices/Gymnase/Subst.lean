import Exercices.Naturels.Transfert

/-!
# Remplacer une variable partout

`subst h` (avec `h : x = 5`) remplace `x` par `5` **partout** (but et hypothèses), et fait disparaître `x`.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.Subst` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Gymnase.Subst` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem subst_exemple (x y : Nat) (h : x = 5) (h2 : x + y = 7) : y = 2 := by
  sorry

end Parcours.Gymnase

#verifier
