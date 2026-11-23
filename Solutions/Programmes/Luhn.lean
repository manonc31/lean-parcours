/- @parcours
titre: La clé de Luhn des cartes bancaires
difficulte: 3
requiert: Programmes.Onze
indice: `doubler_lt` et `doubler_injectif` : seulement 10 chiffres à essayer, `decide`.
indice: `luhn_append` : récurrence sur `l₁` en généralisant `b` ; deux cas selon la parité de la longueur.
indice: `une_faute` : décompose avec `luhn_append`, puis le chiffre modifié a la même contribution modulo 10 ; si elle est doublée, utilise `doubler_injectif`.
-/
import Solutions.Programmes.Definitions

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
-/

namespace Parcours.Prog

def doubler (d : Nat) : Nat := if 2 * d < 10 then 2 * d else 2 * d - 9

def luhn : List Nat → Bool → Nat
  | [], _ => 0
  | d :: l, b => (if b then doubler d else d) + luhn l (!b)

def valide (numero : List Nat) : Bool := luhn numero.reverse false % 10 == 0

theorem exemple_luhn : valide [7, 9, 9, 2, 7, 3, 9, 8, 7, 1, 3] = true := by -- @exo
  decide

theorem doubler_lt : ∀ a, a < 10 → doubler a < 10 := by -- @exo
  decide

theorem doubler_injectif : ∀ a, a < 10 → ∀ c, c < 10 → doubler a = doubler c → a = c := by -- @exo
  decide

theorem luhn_append (l₁ l₂ : List Nat) (b : Bool) :
    luhn (l₁ ++ l₂) b = luhn l₁ b + luhn l₂ (if l₁.length % 2 = 0 then b else !b) := by -- @exo
  induction l₁ generalizing b with
  | nil => simp [luhn]
  | cons d l ih =>
    simp only [List.cons_append, luhn, ih, List.length_cons]
    rcases Nat.mod_two_eq_zero_or_one l.length with h | h
    · have h' : (l.length + 1) % 2 = 1 := by omega
      simp only [h, h', ↓reduceIte, Nat.one_ne_zero, Nat.add_assoc]
    · have h' : (l.length + 1) % 2 = 0 := by omega
      simp only [h, h', ↓reduceIte, Nat.one_ne_zero, Bool.not_not, Nat.add_assoc]

theorem une_faute (l₁ l₂ : List Nat) (a c : Nat) (b : Bool) (ha : a < 10) (hc : c < 10)
    (h : luhn (l₁ ++ a :: l₂) b % 10 = luhn (l₁ ++ c :: l₂) b % 10) : a = c := by -- @exo
  rw [luhn_append, luhn_append] at h
  simp only [luhn] at h
  have da := doubler_lt a ha
  have dc := doubler_lt c hc
  generalize (if l₁.length % 2 = 0 then b else !b) = b' at h
  cases b'
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    omega
  · simp only [↓reduceIte] at h
    exact doubler_injectif a ha c hc (by omega)

end Parcours.Prog

#verifier
