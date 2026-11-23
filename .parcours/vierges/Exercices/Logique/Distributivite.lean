import Exercices.Logique.Equivalence

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

---
*Exercice* `Logique.Distributivite` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Logique.Distributivite` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Logique

variable {P Q R : Prop}

theorem et_ou_distrib : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  sorry

theorem ou_et_distrib : P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by
  sorry

end Parcours.Logique

#verifier
