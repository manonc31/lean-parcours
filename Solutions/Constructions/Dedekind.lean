/- @parcours
titre: Les réels de Dedekind sont complets
difficulte: 4
requiert: Constructions.Racine2Q
indice: Le candidat : la **réunion** des coupures de `S`. `L.ens q := ∃ x, S x ∧ x.ens q`.
indice: Il faut vérifier les 4 propriétés d'une coupure pour `L` : non vide (une coupure de `S` a un élément), pas tout (un élément hors du majorant `M`), descendante, sans maximum.
indice: Utilise `refine ⟨⟨fun q => ∃ x, S x ∧ x.ens q, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩` : 6 buts à traiter un par un.
-/
import Solutions.Constructions.CorpsQ
import Solutions.Listes.Pont

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
    ∃ L : Coupure, (∀ x, S x → x ≤ L) ∧ ∀ M : Coupure, (∀ x, S x → x ≤ M) → L ≤ M := by -- @exo
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨M, hM⟩ := hmaj
  refine ⟨⟨fun q => ∃ x, S x ∧ x.ens q, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · obtain ⟨q, hq⟩ := x0.non_vide
    exact ⟨q, x0, hx0, hq⟩
  · obtain ⟨q, hq⟩ := M.pas_tout
    exact ⟨q, fun ⟨x, hx, hxq⟩ => hq (hM x hx q hxq)⟩
  · rintro p q ⟨x, hx, hxq⟩ hpq
    exact ⟨x, hx, x.descend p q hxq hpq⟩
  · rintro p ⟨x, hx, hxp⟩
    obtain ⟨q, hpq, hq⟩ := x.sans_max p hxp
    exact ⟨q, hpq, x, hx, hq⟩
  · intro x hx q hq
    exact ⟨x, hx, hq⟩
  · rintro M' hM' q ⟨x, hx, hxq⟩
    exact hM' x hx q hxq

end Parcours.Constructions

#verifier
