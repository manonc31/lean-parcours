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

---
*Exercice* `Logique.Curry` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Logique.Curry` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Logique

variable {P Q R : Prop}

theorem curryfication : (P ∧ Q → R) ↔ (P → Q → R) := by
  sorry

theorem ou_impl : (P ∨ Q → R) ↔ (P → R) ∧ (Q → R) := by
  sorry

end Parcours.Logique

#verifier
