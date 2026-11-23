import Exercices.Algorithmes.Definitions

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

---
*Exercice* `Algorithmes.Dichotomie` · difficulté ★★★★☆

💡 Indices : `./parcours indice Algorithmes.Dichotomie` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
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
      (∀ i, dichotomie t x lo hi ≤ i → i < hi → x ≤ t i) := by
  sorry

end Parcours.Algo

#verifier
