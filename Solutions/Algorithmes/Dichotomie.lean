/- @parcours
titre: La recherche dichotomique
difficulte: 4
indice: `fun_induction dichotomie t x lo hi with` : trois cas (on va à droite, on va à gauche, intervalle vide).
indice: Cas « à droite » (`t m < x` avec `m = (lo + hi) / 2`) : l'hypothèse de récurrence parle de l'intervalle `[m + 1, hi)`. Pour les `i` entre `lo` et `m`, utilise la monotonie : `t i ≤ t m < x`.
indice: Cas « à gauche » : symétrique, avec `x ≤ t m ≤ t i` pour `i ≥ m`.
indice: L'hypothèse `lo ≤ hi` doit être transmise aux appels récursifs (`omega`).
-/
import Solutions.Algorithmes.Definitions

/-!
# La recherche dichotomique

Dans un tableau **trié** `t[lo], …, t[hi - 1]`, on cherche la première position où `t i ≥ x`.
On regarde le milieu, et on élimine la moitié de l'intervalle à chaque étape : `log₂ n` étapes.

Un algorithme simple… et notoirement difficile à écrire juste : en 2006, on a découvert un bug
dans la recherche dichotomique de Java, présent depuis 9 ans. Toi, tu vas la **prouver**.

Le tableau est une fonction croissante `t : Nat → Nat`.

## À prouver
`dichotomie_spec` : le résultat `r` est dans `[lo, hi]`, tous les éléments avant `r` sont `< x`,
et tous ceux à partir de `r` sont `≥ x`.

## Ressources
- [Recherche dichotomique (Wikipédia)](https://fr.wikipedia.org/wiki/Recherche_dichotomique)
-/

namespace Parcours.Algo

def dichotomie (t : Nat → Nat) (x : Nat) (lo hi : Nat) : Nat :=
  if lo < hi then
    if t ((lo + hi) / 2) < x then dichotomie t x ((lo + hi) / 2 + 1) hi
    else dichotomie t x lo ((lo + hi) / 2)
  else lo
termination_by hi - lo
decreasing_by all_goals omega

theorem dichotomie_spec (t : Nat → Nat) (x : Nat) (hmono : ∀ i j, i ≤ j → t i ≤ t j)
    (lo hi : Nat) (hle : lo ≤ hi) :
    lo ≤ dichotomie t x lo hi ∧ dichotomie t x lo hi ≤ hi ∧
      (∀ i, lo ≤ i → i < dichotomie t x lo hi → t i < x) ∧
      (∀ i, dichotomie t x lo hi ≤ i → i < hi → x ≤ t i) := by -- @exo
  fun_induction dichotomie t x lo hi with
  | case1 lo hi hlt hm ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih (by omega)
    refine ⟨by omega, h2, ?_, h4⟩
    intro i hi1 hi2
    by_cases hi : i ≤ (lo + hi) / 2
    · exact Nat.lt_of_le_of_lt (hmono _ _ hi) hm
    · exact h3 i (by omega) hi2
  | case2 lo hi hlt hm ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih (by omega)
    refine ⟨h1, by omega, h3, ?_⟩
    intro i hi1 hi2
    by_cases hi : (lo + hi) / 2 ≤ i
    · exact Nat.le_trans (by omega) (hmono _ _ hi)
    · exact h4 i hi1 (by omega)
  | case3 lo hi hlt =>
    refine ⟨Nat.le_refl _, hle, ?_, ?_⟩
    · intro i hi1 hi2
      omega
    · intro i hi1 hi2
      omega

end Parcours.Algo

#verifier
