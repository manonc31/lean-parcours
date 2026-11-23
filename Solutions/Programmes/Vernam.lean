/- @parcours
titre: Le masque jetable
difficulte: 2
requiert: Programmes.Cesar
indice: Récurrence sur `k` en généralisant `m`, puis `cases m`.
indice: Les cas où les longueurs diffèrent sont absurdes : `simp at h`.
indice: Pour les bits : `cases a <;> cases b <;> rfl`.
-/
import Solutions.Programmes.Definitions

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
-/

namespace Parcours.Prog

def masque : List Bool → List Bool → List Bool
  | k :: ks, m :: ms => (k ^^ m) :: masque ks ms
  | _, _ => []

theorem masque_involutif (k m : List Bool) (h : k.length = m.length) :
    masque k (masque k m) = m := by -- @exo
  induction k generalizing m with
  | nil =>
    cases m with
    | nil => rfl
    | cons => simp at h
  | cons a k ih =>
    cases m with
    | nil => simp at h
    | cons b m =>
      simp only [masque]
      rw [ih m (by simpa using h)]
      cases a <;> cases b <;> rfl

theorem masque_secret (m c : List Bool) (h : m.length = c.length) :
    masque (masque m c) m = c := by -- @exo
  induction m generalizing c with
  | nil =>
    cases c with
    | nil => rfl
    | cons => simp at h
  | cons a m ih =>
    cases c with
    | nil => simp at h
    | cons b c =>
      simp only [masque]
      rw [ih c (by simpa using h)]
      cases a <;> cases b <;> rfl

end Parcours.Prog

#verifier
