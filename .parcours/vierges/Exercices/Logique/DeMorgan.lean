import Exercices.Logique.Negation

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

---
*Exercice* `Logique.DeMorgan` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Logique.DeMorgan` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Logique

variable {P Q : Prop}

theorem non_ou : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  sorry

theorem non_et_de_ou (h : ¬P ∨ ¬Q) : ¬(P ∧ Q) := by
  sorry

theorem non_non_tiers_exclu : ¬¬(P ∨ ¬P) := by
  sorry

end Parcours.Logique

#verifier
