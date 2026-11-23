import Exercices.Naturels.Transfert

/-!
# Chercher un lemme avec exact?

`exact?` **cherche** dans la bibliothèque un lemme qui prouve le but, et te propose la ligne à écrire (clique dessus dans l'infoview). Ici, après le Pont, les lemmes de `Nat` sont permis.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.Chercher` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Gymnase.Chercher` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem chercher (a b : Nat) : a * b = b * a := by
  sorry

end Parcours.Gymnase

#verifier
