import Exercices.Fonctions.Definitions

/-!
# Construire des inverses avec l'axiome du choix

Une surjection a un inverse à droite, une injection (de domaine non vide) un inverse à gauche.
Mais pour **construire** ces inverses, il faut **choisir** un antécédent pour chaque `y` :
c'est l'axiome du choix (`Classical.choose`).

## À prouver
1. `inverse_droite (h : Surjective f) : ∃ g : β → α, ∀ y, f (g y) = y`
2. `inverse_gauche [Nonempty α] (h : Injective f) : ∃ g : β → α, ∀ x, g (f x) = x`

## Ressources
- [Axiome du choix (Wikipédia)](https://fr.wikipedia.org/wiki/Axiome_du_choix)

---
*Exercice* `Fonctions.Choix` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Fonctions.Choix` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Fonctions

variable {α β : Type} {f : α → β}

theorem inverse_droite (h : Surjective f) : ∃ g : β → α, ∀ y, f (g y) = y := by
  sorry

theorem inverse_gauche [Nonempty α] (h : Injective f) : ∃ g : β → α, ∀ x, g (f x) = x := by
  sorry

end Parcours.Fonctions

#verifier
