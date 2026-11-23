import Exercices.Programmes.Definitions

/-!
# Le masque jetable

Le **masque jetable** (Vernam, 1917) est le seul chiffrement **parfaitement sûr** : on combine
chaque bit du message avec un bit d'une clé aléatoire aussi longue que le message, par OU
exclusif (`^^`). Pour déchiffrer, on refait la même opération avec la même clé.

Pourquoi est-il parfaitement sûr ? Parce que **n'importe quel** message aurait pu donner le
chiffré observé, avec une clé bien choisie : l'espion n'apprend rien.

## À prouver
1. `masque_involutif : masque k (masque k m) = m` (si `k` et `m` ont la même longueur)
2. `masque_secret : masque (masque m c) m = c` : pour tout message `m` et tout chiffré `c`,
   la clé `masque m c` transforme `m` en `c`.

## Ressources
- [Masque jetable (Wikipédia)](https://fr.wikipedia.org/wiki/Masque_jetable)

---
*Exercice* `Programmes.Vernam` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Programmes.Vernam` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

def masque : List Bool → List Bool → List Bool
  | k :: ks, m :: ms => (k ^^ m) :: masque ks ms
  | _, _ => []

theorem masque_involutif (k m : List Bool) (h : k.length = m.length) :
    masque k (masque k m) = m := by
  sorry

theorem masque_secret (m c : List Bool) (h : m.length = c.length) :
    masque (masque m c) m = c := by
  sorry

end Parcours.Prog

#verifier
