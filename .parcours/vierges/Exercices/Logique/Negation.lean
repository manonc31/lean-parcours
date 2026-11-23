import ParcoursOutils

/-!
# Faux et négation

- `False` est la proposition **sans preuve**. Si tu arrives à prouver `False`, tes hypothèses
  sont contradictoires, et tu peux alors prouver n'importe quoi (`False.elim`, ou la tactique `exfalso`).
- `¬P` (tapé `\not`) est **défini** comme `P → False`.

Tactiques utiles : `exfalso` (remplace le but par `False`), `contradiction`
(trouve tout seul deux hypothèses contradictoires), `absurd`.

## À prouver
1. `faux_elim : False → P`
2. `non_contradiction : ¬(P ∧ ¬P)`
3. `contraposee : (P → Q) → (¬Q → ¬P)`
4. `double_neg_intro : P → ¬¬P`
5. `triple_neg : ¬¬¬P ↔ ¬P`

Remarque : la réciproque `¬¬P → P` n'est **pas** prouvable ainsi ! Il faudra la logique classique.

## Ressources
- [Logique intuitionniste (Wikipédia)](https://fr.wikipedia.org/wiki/Logique_intuitionniste)

---
*Exercice* `Logique.Negation` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Logique.Negation` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Logique

variable {P Q : Prop}

theorem faux_elim (h : False) : P := by
  sorry

theorem non_contradiction : ¬(P ∧ ¬P) := by
  sorry

theorem contraposee (h : P → Q) : ¬Q → ¬P := by
  sorry

theorem double_neg_intro (hp : P) : ¬¬P := by
  sorry

theorem triple_neg : ¬¬¬P ↔ ¬P := by
  sorry

end Parcours.Logique

#verifier
