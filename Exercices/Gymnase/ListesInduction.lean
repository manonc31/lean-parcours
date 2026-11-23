import Exercices.Listes.Pont

/-!
# Récurrence sur une liste

`induction l with | nil => … | cons x l ih => …` : le cas de la liste vide, et le cas « un élément devant une liste pour laquelle c'est vrai ».

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.ListesInduction` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Gymnase.ListesInduction` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem map_id' (l : List Nat) : l.map (fun x => x) = l := by
  sorry

end Parcours.Gymnase

#verifier
