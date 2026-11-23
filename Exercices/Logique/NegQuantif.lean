import Exercices.Logique.Classique

/-!
# Négation et quantificateurs

« Il n'existe pas de x tel que p(x) » ⟺ « pour tout x, non p(x) ». C'est constructif.

« Ce n'est pas vrai que tout x vérifie p » ⟺ « il existe un x qui ne vérifie pas p ».
Le sens `→` demande la logique classique : on affirme l'existence d'un `x` sans savoir le construire !

## À prouver
1. `non_existe : (¬∃ x, p x) ↔ ∀ x, ¬p x`
2. `non_pourtout : (¬∀ x, p x) ↔ ∃ x, ¬p x`

---
*Exercice* `Logique.NegQuantif` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Logique.NegQuantif` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Logique

variable {α : Type} {p : α → Prop}

theorem non_existe : (¬∃ x, p x) ↔ ∀ x, ¬p x := by
  sorry

theorem non_pourtout : (¬∀ x, p x) ↔ ∃ x, ¬p x := by
  sorry

end Parcours.Logique

#verifier
