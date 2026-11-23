import Exercices.Programmes.Definitions

/-!
# La clé de Luhn des cartes bancaires

Le dernier chiffre d'un numéro de carte bancaire (ou de SIRET) est une **clé de contrôle** :
la formule de Luhn. En partant de la droite, on double un chiffre sur deux (si le double dépasse
9, on retire 9), on additionne tout, et le total doit être multiple de 10.

À quoi ça sert ? À détecter les **fautes de frappe** : si on se trompe sur un seul chiffre, le
total change forcément modulo 10. C'est ce qu'on va prouver.

Ici, le numéro est donné **à l'envers** (chiffre de droite en tête) ; le booléen dit si le
chiffre courant doit être doublé.

## À prouver
1. `exemple_luhn` : le numéro 79927398713 est valide.
2. `doubler_lt`, `doubler_injectif` : doubler un chiffre donne un chiffre, et deux chiffres
   différents donnent des résultats différents.
3. `luhn_append` : la clé d'une concaténation.
4. `une_faute` : changer un seul chiffre change la clé modulo 10.

## Ressources
- [Formule de Luhn (Wikipédia)](https://fr.wikipedia.org/wiki/Formule_de_Luhn)

---
*Exercice* `Programmes.Luhn` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Programmes.Luhn` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

def doubler (d : Nat) : Nat := if 2 * d < 10 then 2 * d else 2 * d - 9

def luhn : List Nat → Bool → Nat
  | [], _ => 0
  | d :: l, b => (if b then doubler d else d) + luhn l (!b)

def valide (numero : List Nat) : Bool := luhn numero.reverse false % 10 == 0

theorem exemple_luhn : valide [7, 9, 9, 2, 7, 3, 9, 8, 7, 1, 3] = true := by
  sorry

theorem doubler_lt : ∀ a, a < 10 → doubler a < 10 := by
  sorry

theorem doubler_injectif : ∀ a, a < 10 → ∀ c, c < 10 → doubler a = doubler c → a = c := by
  sorry

theorem luhn_append (l₁ l₂ : List Nat) (b : Bool) :
    luhn (l₁ ++ l₂) b = luhn l₁ b + luhn l₂ (if l₁.length % 2 = 0 then b else !b) := by
  sorry

theorem une_faute (l₁ l₂ : List Nat) (a c : Nat) (b : Bool) (ha : a < 10) (hc : c < 10)
    (h : luhn (l₁ ++ a :: l₂) b % 10 = luhn (l₁ ++ c :: l₂) b % 10) : a = c := by
  sorry

end Parcours.Prog

#verifier
