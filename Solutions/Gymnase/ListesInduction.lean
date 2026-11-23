/- @parcours
titre: Récurrence sur une liste
difficulte: 2
requiert: Gymnase.Simp
indice: `induction l with`.
indice: Cas `cons` : `simp [ih]`.
-/
import Solutions.Listes.Pont

/-!
# Récurrence sur une liste

`induction l with | nil => … | cons x l ih => …` : le cas de la liste vide, et le cas « un élément devant une liste pour laquelle c'est vrai ».

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem map_id' (l : List Nat) : l.map (fun x => x) = l := by -- @exo
  induction l with
  | nil => rfl
  | cons x l ih => simp [ih]

end Parcours.Gymnase

#verifier
