import Exercices.Logique.NegQuantif

/-!
# 🌉 Le grand examen de logique

Bravo, tu as fait le tour de la logique ! Dernier examen, et en récompense, ce **Pont** débloque
le jeton **`logique`** : pour tous les exercices qui en dépendent, tu pourras utiliser librement
les lemmes de logique de la bibliothèque (`and_comm`, `not_not`, `forall_and`…) et laisser
`simp` manipuler les connecteurs, **sans perdre ton étoile** ⭐. Tu les as tous recodés, tu as gagné le droit de t'en servir.

## À prouver
1. `bilan_cas : (P → Q) → (¬P → Q) → Q`
2. `bilan_absurde : ¬(P ↔ ¬P)`
3. `bilan_existe : (∃ x, p x → q) ↔ ((∀ x, p x) → q)` (avec `α` non vide)

---
*Exercice* `Logique.Bilan` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Logique.Bilan` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Logique

variable {P Q : Prop}

theorem bilan_cas (h1 : P → Q) (h2 : ¬P → Q) : Q := by
  sorry

theorem bilan_absurde : ¬(P ↔ ¬P) := by
  sorry

theorem bilan_existe {α : Type} [Nonempty α] {p : α → Prop} {q : Prop} :
    (∃ x, p x → q) ↔ ((∀ x, p x) → q) := by
  sorry

end Parcours.Logique

#verifier
