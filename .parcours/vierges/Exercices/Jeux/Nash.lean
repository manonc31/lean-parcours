import Exercices.Recurrence.Definitions

/-!
# Le dilemme du prisonnier

Deux complices sont interrogés séparément. Chacun peut se **taire** ou **trahir** :
- les deux se taisent : 1 an de prison chacun ;
- un seul trahit : il est libéré, l'autre prend 3 ans ;
- les deux trahissent : 2 ans chacun.

Un **équilibre de Nash** : aucun joueur ne gagne à changer seul de stratégie.
Le paradoxe : le seul équilibre est (trahir, trahir)… alors que (se taire, se taire) est meilleur
pour les deux ! (Nash, prix Nobel 1994, et le film *Un homme d'exception*.)

`true` = trahir, `false` = se taire. `annees a b` : années de prison pour un joueur qui joue `a`
contre un adversaire qui joue `b`.

## À prouver
1. `trahir_domine` : quoi que fasse l'autre, trahir est toujours au moins aussi bon.
2. `nash_unique` : (trahir, trahir) est l'unique équilibre de Nash.
3. `pareto` : pourtant, se taire tous les deux est strictement meilleur pour les deux.

## Ressources
- [Dilemme du prisonnier (Wikipédia)](https://fr.wikipedia.org/wiki/Dilemme_du_prisonnier)
- [Équilibre de Nash (Wikipédia)](https://fr.wikipedia.org/wiki/%C3%89quilibre_de_Nash)

---
*Exercice* `Jeux.Nash` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Jeux.Nash` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Jeux

/-- Années de prison pour qui joue `a` contre `b` (`true` = trahir). -/
def annees : Bool → Bool → Nat
  | false, false => 1
  | false, true => 3
  | true, false => 0
  | true, true => 2

/-- `(a, b)` est un équilibre de Nash : aucun des deux n'améliore son sort en changeant seul. -/
def Nash (a b : Bool) : Prop := (∀ a', annees a b ≤ annees a' b) ∧ (∀ b', annees b a ≤ annees b' a)

instance (a b : Bool) : Decidable (Nash a b) := by unfold Nash; infer_instance

theorem trahir_domine (b : Bool) : annees true b ≤ annees false b := by
  sorry

theorem nash_unique (a b : Bool) : Nash a b ↔ (a = true ∧ b = true) := by
  sorry

theorem pareto : annees false false < annees true true := by
  sorry

end Parcours.Jeux

#verifier
