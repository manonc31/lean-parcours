/- @parcours
titre: Lois de De Morgan (constructives)
difficulte: 2
indice: `non_ou`, sens `→` : pour prouver `¬P`, `intro hp`, puis contredis `h` avec `Or.inl hp`.
indice: `non_ou`, sens `←` : `rintro ⟨hnp, hnq⟩ (hp | hq)`.
indice: `non_non_tiers_exclu` : `intro h`, puis `apply h`, puis `right`, puis `intro hp`… et `h` sert encore une fois !
-/
import Solutions.Logique.Negation

/-!
# Lois de De Morgan (la partie constructive)

Deux des quatre implications de De Morgan se prouvent sans logique classique. Les voici.
Et un résultat étonnant : on ne peut pas prouver `P ∨ ¬P` sans logique classique…
mais on peut prouver qu'il est **impossible qu'il soit faux** !

## À prouver
1. `non_ou : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q`
2. `non_et_de_ou : ¬P ∨ ¬Q → ¬(P ∧ Q)`
3. `non_non_tiers_exclu : ¬¬(P ∨ ¬P)`

## Ressources
- [Lois de De Morgan (Wikipédia)](https://fr.wikipedia.org/wiki/Lois_de_De_Morgan)
-/

namespace Parcours.Logique

variable {P Q : Prop}

theorem non_ou : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by -- @exo
  constructor
  · intro h
    exact ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩
  · rintro ⟨hnp, hnq⟩ (hp | hq)
    · exact hnp hp
    · exact hnq hq

theorem non_et_de_ou (h : ¬P ∨ ¬Q) : ¬(P ∧ Q) := by -- @exo
  rintro ⟨hp, hq⟩
  rcases h with hnp | hnq
  · exact hnp hp
  · exact hnq hq

theorem non_non_tiers_exclu : ¬¬(P ∨ ¬P) := by -- @exo
  intro h
  apply h
  right
  intro hp
  exact h (Or.inl hp)

end Parcours.Logique

#verifier
