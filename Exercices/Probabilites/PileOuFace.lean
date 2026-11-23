import Exercices.Probabilites.Definitions

/-!
# Pile ou face et le triangle de Pascal

On lance `n` fois une pièce. Il y a `2ⁿ` suites possibles, et exactement `C(n, k)` d'entre elles
contiennent `k` « pile ». Donc `P(k piles) = C(n, k) / 2ⁿ` : c'est la **loi binomiale**.

`mots n` est la liste de tous les mots de longueur `n` sur `{false, true}` (`true` = pile).

## À prouver
1. `longueur_mots : (mots n).length = 2 ^ n`
2. `nombre_de_piles : (mots n).countP (fun w => w.count true == k) = binom n k`

## Ressources
- [Loi binomiale (Wikipédia)](https://fr.wikipedia.org/wiki/Loi_binomiale)

---
*Exercice* `Probabilites.PileOuFace` · difficulté ★★★★☆

💡 Indices : `./parcours indice Probabilites.PileOuFace` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Proba

open Parcours.Combi

def mots : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (mots n).map (false :: ·) ++ (mots n).map (true :: ·)

theorem longueur_mots (n : Nat) : (mots n).length = 2 ^ n := by
  sorry

theorem nombre_de_piles (n k : Nat) :
    (mots n).countP (fun w => w.count true == k) = binom n k := by
  sorry

end Parcours.Proba

#verifier
