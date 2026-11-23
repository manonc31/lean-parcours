/- @parcours
titre: Le mélange parfait du magicien
difficulte: 2
requiert: Programmes.Carrousel
indice: `longueur_entrelacer` : récurrence sur `xs` en généralisant `ys`, puis `cases ys`.
indice: Les deux derniers sont des calculs : `decide +kernel`.
-/
import Solutions.Programmes.Definitions

/-!
# Le mélange parfait du magicien

Un magicien coupe un jeu de 52 cartes en deux moitiés égales et les entrelace parfaitement
(carte du dessus, puis une de l'autre moitié, etc.) : c'est le **faro**. Miracle : après **8**
mélanges parfaits, le jeu est revenu dans l'ordre de départ ! Les magiciens s'en servent pour
avoir l'air de mélanger.

## À prouver
1. `longueur_entrelacer`, `longueur_melanger` : on ne perd aucune carte.
2. `magicien` : 8 mélanges ramènent le jeu à l'ordre initial,
3. `pas_avant` : et pas moins de 8.

## Ressources
- [Mélange faro (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Faro_shuffle)
-/

namespace Parcours.Prog

def entrelacer {α : Type} : List α → List α → List α
  | x :: xs, y :: ys => x :: y :: entrelacer xs ys
  | xs, [] => xs
  | [], ys => ys

def melanger {α : Type} (l : List α) : List α :=
  entrelacer (l.take (l.length / 2)) (l.drop (l.length / 2))

theorem longueur_entrelacer {α : Type} (xs ys : List α) :
    (entrelacer xs ys).length = xs.length + ys.length := by -- @exo
  induction xs generalizing ys with
  | nil => cases ys <;> simp [entrelacer]
  | cons x xs ih =>
    cases ys with
    | nil => simp [entrelacer]
    | cons y ys =>
      simp only [entrelacer, List.length_cons, ih]
      omega

theorem longueur_melanger {α : Type} (l : List α) : (melanger l).length = l.length := by -- @exo
  simp only [melanger, longueur_entrelacer, List.length_take, List.length_drop]
  omega

theorem magicien : repeter melanger 8 (List.range 52) = List.range 52 := by -- @exo
  decide +kernel

theorem pas_avant : ∀ k, k < 7 → repeter melanger (k + 1) (List.range 52) ≠ List.range 52 := by -- @exo
  decide +kernel

end Parcours.Prog

#verifier
