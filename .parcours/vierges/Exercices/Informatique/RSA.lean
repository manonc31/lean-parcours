import Exercices.Listes.Pont
import Exercices.Recurrence.Definitions

/-!
# RSA en miniature

RSA (Rivest, Shamir, Adleman, 1977) protège tes paiements en ligne. Version jouet : `p = 61`,
`q = 53`, `n = pq = 3233`. La clé publique est `e = 17`, la clé secrète `d = 2753`, avec
`e × d ≡ 1 (mod (p − 1)(q − 1))`. Chiffrer `m`, c'est calculer `mᵉ mod n` ; déchiffrer, `cᵈ mod n`.
Le miracle (petit théorème de Fermat) : on retrouve toujours `m`.

Pour calculer vite, on utilise l'exponentiation rapide modulaire (avec une réserve de calcul).

## À prouver
1. `cles : 61 * 53 = 3233 ∧ 17 * 2753 % (60 * 52) = 1`
2. `exemple` : le message 65 est chiffré en 2790, qui se déchiffre en 65.
3. `rsa` : **tous** les messages `m < 3233` se déchiffrent correctement (on les vérifie par
   paquets de 100, pour ne pas essouffler le noyau de Lean).

## Ressources
- [Chiffrement RSA (Wikipédia)](https://fr.wikipedia.org/wiki/Chiffrement_RSA)

---
*Exercice* `Informatique.RSA` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Informatique.RSA` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Info

/-- `puissMod f a k m = a^k mod m`, par exponentiation rapide (`f` : réserve de calcul). -/
def puissMod : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, m => 1 % m
  | f + 1, a, k, m =>
    if k = 0 then 1 % m
    else
      let r := puissMod f a (k / 2) m
      if k % 2 = 0 then r * r % m else r * r * a % m

def chiffrer (m : Nat) : Nat := puissMod 20 m 17 3233
def dechiffrer (c : Nat) : Nat := puissMod 20 c 2753 3233

theorem cles : 61 * 53 = 3233 ∧ 17 * 2753 % (60 * 52) = 1 := by
  sorry

theorem exemple : chiffrer 65 = 2790 ∧ dechiffrer 2790 = 65 := by
  sorry

theorem par_centaines : ∀ k, k < 33 → ∀ j, j < 100 → 100 * k + j < 3233 →
    dechiffrer (chiffrer (100 * k + j)) = 100 * k + j := by
  sorry

theorem rsa (m : Nat) (h : m < 3233) : dechiffrer (chiffrer m) = m := by
  sorry

end Parcours.Info

#verifier
