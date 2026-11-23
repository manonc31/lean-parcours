/- @parcours
titre: Les entiers relatifs
difficulte: 1
genre: cours
-/
import Solutions.Constructions.RelationZ

/-!
# Les entiers relatifs (cours)

Grâce à ta relation d'équivalence, on définit `Zr` comme le **quotient** de `Nat × Nat` par `~` :
un élément de `Zr` est une « classe » de couples équivalents. `Zr.mk a b` est la classe de `(a, b)`,
c'est-à-dire l'entier relatif `a - b`.

## Outils
- `Zr.mk_eq_mk : Zr.mk a b = Zr.mk c d ↔ a + d = c + b` : pour prouver une égalité dans `Zr`.
- `Zr.existe x : ∃ a b, x = Zr.mk a b` : tout élément s'écrit `Zr.mk a b`.
  Utilisation : `obtain ⟨a, b, rfl⟩ := Zr.existe x`.

Une opération sur `Zr` se définit sur les couples, à condition de prouver qu'elle **respecte** `~`
(sinon le résultat dépendrait du représentant choisi !). Ce sont les exercices suivants.

## Ressources
- [Ensemble quotient (Wikipédia)](https://fr.wikipedia.org/wiki/Relation_d%27%C3%A9quivalence#Ensemble_quotient)
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/), chapitre *Axioms and Computation* (section *Quotients*).
-/

namespace Parcours.Constructions

instance setoidZ : Setoid (Nat × Nat) := ⟨RelZ, ⟨relZ_refl, relZ_symm, relZ_trans⟩⟩

/-- Les entiers relatifs, construits comme quotient. -/
def Zr : Type := Quotient setoidZ

/-- `Zr.mk a b` représente `a - b`. -/
def Zr.mk (a b : Nat) : Zr := Quotient.mk setoidZ (a, b)

theorem Zr.mk_eq_mk {a b c d : Nat} : Zr.mk a b = Zr.mk c d ↔ a + d = c + b :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound (s := setoidZ) h⟩

theorem Zr.existe (x : Zr) : ∃ a b, x = Zr.mk a b :=
  Quotient.inductionOn x (fun ⟨a, b⟩ => ⟨a, b, rfl⟩)

instance : OfNat Zr 0 := ⟨Zr.mk 0 0⟩
instance : OfNat Zr 1 := ⟨Zr.mk 1 0⟩

theorem Zr.zero_def : (0 : Zr) = Zr.mk 0 0 := rfl
theorem Zr.one_def : (1 : Zr) = Zr.mk 1 0 := rfl

end Parcours.Constructions
