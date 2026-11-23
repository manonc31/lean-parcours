import Exercices.Combinatoire.Definitions

/-!
# Probabilités et dénombrement (cours)

Quand toutes les issues sont **équiprobables**, une probabilité est une proportion :
`P(E) = (nombre d'issues où E est vrai) / (nombre total d'issues)`.

On représente l'**univers** Ω (toutes les issues) par une liste, et un événement par une fonction
`E : α → Bool`. `Ω.countP E` compte les issues favorables.

Pour éviter les fractions, on écrit `P(E) = p / q` en **produit en croix** :
`ProbaEst Ω E p q` signifie `Ω.countP E * q = p * Ω.length`. C'est **décidable** : pour un univers
donné, la tactique `decide` fait tout le calcul (par exemple sur les 36 issues de deux dés).

Probabilité conditionnelle : `P(A | B) = P(A et B) / P(B)` ; on la calcule en se restreignant à
l'univers `Ω.filter B`.

## Ressources
- [Probabilité (Wikipédia)](https://fr.wikipedia.org/wiki/Probabilit%C3%A9)
- [Équiprobabilité (Wikipédia)](https://fr.wikipedia.org/wiki/%C3%89quiprobabilit%C3%A9)

---
*Exercice* `Probabilites.Definitions` · difficulté ★☆☆☆☆
-/

namespace Parcours.Proba

/-- `ProbaEst Ω E p q` : dans l'univers Ω (équiprobable), `P(E) = p / q`. -/
def ProbaEst {α : Type} (Ω : List α) (E : α → Bool) (p q : Nat) : Prop :=
  Ω.countP E * q = p * Ω.length

instance {α : Type} (Ω : List α) (E : α → Bool) (p q : Nat) : Decidable (ProbaEst Ω E p q) :=
  inferInstanceAs (Decidable (_ = _))

/-- Un dé à six faces. -/
def de : List Nat := [1, 2, 3, 4, 5, 6]

/-- Les 36 issues d'un lancer de deux dés. -/
def deuxDes : List (Nat × Nat) := de.flatMap (fun a => de.map (fun b => (a, b)))

end Parcours.Proba
