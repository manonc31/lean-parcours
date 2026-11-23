/- @parcours
titre: Distributivité
difficulte: 2
indice: `rintro` combine `intro` et `rcases` : `rintro ⟨hp, hq | hr⟩` introduit une hypothèse `P ∧ (Q ∨ R)` et la découpe d'un coup en deux cas.
indice: Pour `ou_et_distrib`, dans le sens `←`, `rintro ⟨hp | hq, hp' | hr⟩` produit 4 cas. Dans 3 d'entre eux, tu as une preuve de `P`.
-/
import Solutions.Logique.Equivalence

/-!
# Distributivité de ∧ et ∨

Comme `a × (b + c) = a × b + a × c`, le « et » se distribue sur le « ou »… et réciproquement !

La tactique **`rintro`** est très pratique : `rintro ⟨hp, hq | hr⟩` introduit une hypothèse
et la découpe selon le motif donné.

## À prouver
1. `et_ou_distrib : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R)`
2. `ou_et_distrib : P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R)`

## Ressources
- [Algèbre de Boole (Wikipédia)](https://fr.wikipedia.org/wiki/Alg%C3%A8bre_de_Boole_%28logique%29)
-/

namespace Parcours.Logique

variable {P Q R : Prop}

theorem et_ou_distrib : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by -- @exo
  constructor
  · rintro ⟨hp, hq | hr⟩
    · exact Or.inl ⟨hp, hq⟩
    · exact Or.inr ⟨hp, hr⟩
  · rintro (⟨hp, hq⟩ | ⟨hp, hr⟩)
    · exact ⟨hp, Or.inl hq⟩
    · exact ⟨hp, Or.inr hr⟩

theorem ou_et_distrib : P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by -- @exo
  constructor
  · rintro (hp | ⟨hq, hr⟩)
    · exact ⟨Or.inl hp, Or.inl hp⟩
    · exact ⟨Or.inr hq, Or.inr hr⟩
  · rintro ⟨hp | hq, hp' | hr⟩
    · exact Or.inl hp
    · exact Or.inl hp
    · exact Or.inl hp'
    · exact Or.inr ⟨hq, hr⟩

end Parcours.Logique

#verifier
