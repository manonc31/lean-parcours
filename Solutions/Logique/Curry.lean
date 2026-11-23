/- @parcours
titre: Curryfication
difficulte: 1
requiert: Logique.Et, Logique.Ou
indice: `constructor`, puis dans chaque sens, `intro` tout ce qui peut l'être.
indice: `rintro h ⟨hp, hq⟩` introduit `h` puis découpe le `∧`.
-/
import ParcoursOutils

/-!
# Curryfication

Avoir `P ∧ Q → R`, c'est la même chose qu'avoir `P → Q → R` : une fonction de deux
arguments est une fonction qui renvoie une fonction. (Nommé d'après le logicien Haskell Curry.)

`P → Q → R` se lit `P → (Q → R)`.

## À prouver
1. `curryfication : (P ∧ Q → R) ↔ (P → Q → R)`
2. `ou_impl : (P ∨ Q → R) ↔ (P → R) ∧ (Q → R)`

## Ressources
- [Curryfication (Wikipédia)](https://fr.wikipedia.org/wiki/Curryfication)
-/

namespace Parcours.Logique

variable {P Q R : Prop}

theorem curryfication : (P ∧ Q → R) ↔ (P → Q → R) := by -- @exo
  constructor
  · intro h hp hq
    exact h ⟨hp, hq⟩
  · rintro h ⟨hp, hq⟩
    exact h hp hq

theorem ou_impl : (P ∨ Q → R) ↔ (P → R) ∧ (Q → R) := by -- @exo
  constructor
  · intro h
    exact ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩
  · rintro ⟨hpr, hqr⟩ (hp | hq)
    · exact hpr hp
    · exact hqr hq

end Parcours.Logique

#verifier
