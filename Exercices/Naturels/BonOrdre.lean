import Exercices.Naturels.RecurrenceForte
import Exercices.Naturels.LeTotal

/-!
# Le principe du bon ordre

> Toute partie non vide de ℕ a un plus petit élément.

C'est équivalent à la récurrence (forte). Faux dans ℤ (pas de plus petit entier relatif),
faux dans les rationnels positifs (pas de plus petit rationnel > 0).

## À prouver
`bon_ordre (P : ℕ → Prop) (h : ∃ n, P n) : ∃ m, P m ∧ ∀ k, P k → m ≤ k`

## Ressources
- [Bon ordre (Wikipédia)](https://fr.wikipedia.org/wiki/Bon_ordre)

---
*Exercice* `Naturels.BonOrdre` · difficulté ★★★★☆

💡 Indices : `./parcours indice Naturels.BonOrdre` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.ℕ

theorem bon_ordre (P : ℕ → Prop) (h : ∃ n, P n) : ∃ m, P m ∧ ∀ k, P k → m ≤ k := by
  sorry

end Parcours.ℕ

#verifier
