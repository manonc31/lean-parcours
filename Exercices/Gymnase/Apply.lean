import ParcoursOutils

/-!
# Raisonner à rebours avec apply

`apply hqr` : « pour prouver `R`, il suffit de prouver `Q` ». Le but devient `Q`.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.Apply` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Gymnase.Apply` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem apply_exemple (P Q R : Prop) (hpq : P → Q) (hqr : Q → R) (hp : P) : R := by
  sorry

end Parcours.Gymnase

#verifier
