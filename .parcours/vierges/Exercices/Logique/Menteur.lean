import ParcoursOutils

/-!
# Le paradoxe du menteur

Épiménide le Crétois dit : « Tous les Crétois sont menteurs. » Version plus radicale : « Cette
phrase est fausse. » Si elle est vraie, elle est fausse ; si elle est fausse, elle est vraie. En
logique, aucune proposition ne peut être équivalente à sa propre négation.

## À prouver
`menteur : ¬ (P ↔ ¬P)`

---
*Exercice* `Logique.Menteur` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Logique.Menteur` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Logique

theorem menteur (P : Prop) : ¬ (P ↔ ¬P) := by
  sorry

end Parcours.Logique

#verifier
