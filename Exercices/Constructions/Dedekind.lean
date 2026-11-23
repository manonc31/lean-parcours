import Exercices.Constructions.CorpsQ
import Exercices.Listes.Pont

/-!
# Les réels de Dedekind sont complets

Comment combler les « trous » de ℚ comme `√2` ? Richard Dedekind (1872) : un réel est une
**coupure**, c'est-à-dire l'ensemble des rationnels « strictement à sa gauche ». Par exemple
`√2` est la coupure `{q | q < 0 ∨ q² < 2}`.

Une coupure `x` (ici sur les rationnels `Rat` de Lean) est un ensemble `x.ens` de rationnels :
- non vide, et pas tous les rationnels ;
- **descendant** : si `q ∈ x` et `p < q` alors `p ∈ x` ;
- **sans maximum**.

Et `x ≤ y` signifie `x.ens ⊆ y.ens`.

Le théorème qui fait des réels les réels : **toute partie non vide et majorée a une borne
supérieure** (ce qui est faux dans ℚ : `{q | q² < 2}` n'a pas de borne sup rationnelle).

## À prouver
`borne_superieure (S : Coupure → Prop) (hne : ∃ x, S x) (hmaj : ∃ M, ∀ x, S x → x ≤ M) :
  ∃ L, (∀ x, S x → x ≤ L) ∧ ∀ M, (∀ x, S x → x ≤ M) → L ≤ M`

## Ressources
- [Coupure de Dedekind (Wikipédia)](https://fr.wikipedia.org/wiki/Coupure_de_Dedekind)
- [Construction des nombres réels (Wikipédia)](https://fr.wikipedia.org/wiki/Construction_des_nombres_r%C3%A9els)

---
*Exercice* `Constructions.Dedekind` · difficulté ★★★★☆

💡 Indices : `./parcours indice Constructions.Dedekind` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Constructions

/-- Une coupure de Dedekind : un nombre réel. -/
structure Coupure where
  ens : Rat → Prop
  non_vide : ∃ q, ens q
  pas_tout : ∃ q, ¬ens q
  descend : ∀ p q, ens q → p < q → ens p
  sans_max : ∀ p, ens p → ∃ q, p < q ∧ ens q

instance : LE Coupure := ⟨fun x y => ∀ q, x.ens q → y.ens q⟩

theorem borne_superieure (S : Coupure → Prop) (hne : ∃ x, S x) (hmaj : ∃ M : Coupure, ∀ x, S x → x ≤ M) :
    ∃ L : Coupure, (∀ x, S x → x ≤ L) ∧ ∀ M : Coupure, (∀ x, S x → x ≤ M) → L ≤ M := by
  sorry

end Parcours.Constructions

#verifier
