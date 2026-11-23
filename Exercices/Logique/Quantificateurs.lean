import ParcoursOutils

/-!
# « Tout le monde aime quelqu'un »

« Il existe quelqu'un que tout le monde aime » entraîne « tout le monde aime quelqu'un ». Mais
la réciproque est **fausse** : chacun peut aimer une personne différente ! L'ordre des
quantificateurs `∀` et `∃` compte.

## À prouver
1. `inversion : (∃ y, ∀ x, R x y) → ∀ x, ∃ y, R x y`
2. `pas_reciproque` : avec `R x y := (x = y)` sur `Bool`, chacun « s'aime lui-même » mais personne
   n'est aimé de tous.

---
*Exercice* `Logique.Quantificateurs` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Logique.Quantificateurs` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Logique

theorem inversion {α : Type} (R : α → α → Prop) (h : ∃ y, ∀ x, R x y) : ∀ x, ∃ y, R x y := by
  sorry

theorem pas_reciproque : (∀ x : Bool, ∃ y : Bool, x = y) ∧ ¬ ∃ y : Bool, ∀ x : Bool, x = y := by
  sorry

end Parcours.Logique

#verifier
