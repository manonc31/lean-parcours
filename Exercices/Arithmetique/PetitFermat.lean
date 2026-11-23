import Exercices.Arithmetique.BinomPremier
import Exercices.Arithmetique.Congruences
import Exercices.Combinatoire.Newton

/-!
# Le petit théorème de Fermat

> Si `p` est premier, alors `aᵖ ≡ a (mod p)` pour tout entier `a`.

Énoncé par Fermat en 1640 (« je vous en envoierois la démonstration, si je n'appréhendois d'être
trop long »), prouvé par Euler en 1736. C'est la base du chiffrement **RSA** et des tests de primalité.

La preuve passe par le « rêve de l'étudiant » : modulo `p`, `(a + b)ᵖ ≡ aᵖ + bᵖ` !

## À prouver
1. `reve_etudiant : Premier p → (a + b) ^ p ≡ a ^ p + b ^ p [mod p]`
2. `petit_fermat : Premier p → a ^ p ≡ a [mod p]`

## Ressources
- [Petit théorème de Fermat (Wikipédia)](https://fr.wikipedia.org/wiki/Petit_th%C3%A9or%C3%A8me_de_Fermat)
- [Chiffrement RSA (Wikipédia)](https://fr.wikipedia.org/wiki/Chiffrement_RSA)

---
*Exercice* `Arithmetique.PetitFermat` · difficulté ★★★★☆

💡 Indices : `./parcours indice Arithmetique.PetitFermat` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Arith

open Parcours.Combi

theorem reve_etudiant {p : Nat} (hp : Premier p) (a b : Nat) :
    (a + b) ^ p ≡ a ^ p + b ^ p [mod p] := by
  sorry

theorem petit_fermat {p : Nat} (hp : Premier p) (a : Nat) : a ^ p ≡ a [mod p] := by
  sorry

end Parcours.Arith

#verifier
