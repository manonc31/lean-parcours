import Exercices.Programmes.Definitions

/-!
# La clé ISBN

Le numéro ISBN-10 d'un livre a une clé de contrôle : `10 d₁ + 9 d₂ + ⋯ + 1 d₁₀` doit être
multiple de 11. Elle détecte non seulement une faute de frappe, mais aussi l'**inversion de deux
chiffres voisins** (l'erreur la plus courante quand on recopie un numéro) : échanger `a` et `b`
change la somme de `a − b`, qui n'est jamais multiple de 11 si `a ≠ b`.

## À prouver
1. `exemple_isbn` : `0-306-40615-2` est un ISBN valide (c'est l'exemple de Wikipédia).
2. `isbnSomme_append` : la somme d'une concaténation.
3. `inversion` : échanger deux chiffres voisins différents change la clé.

## Ressources
- [International Standard Book Number (Wikipédia)](https://fr.wikipedia.org/wiki/International_Standard_Book_Number)

---
*Exercice* `Programmes.ISBN` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Programmes.ISBN` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

def isbnSomme : List Nat → Nat
  | [] => 0
  | d :: r => (r.length + 1) * d + isbnSomme r

/-- La contribution de `l` quand on lui ajoute `k` chiffres à droite. -/
def poids : List Nat → Nat → Nat
  | [], _ => 0
  | d :: r, k => (r.length + k + 1) * d + poids r k

def isbnValide (l : List Nat) : Bool := l.length == 10 && isbnSomme l % 11 == 0

theorem exemple_isbn : isbnValide [0, 3, 0, 6, 4, 0, 6, 1, 5, 2] = true := by
  sorry

theorem isbnSomme_append (l x : List Nat) : isbnSomme (l ++ x) = isbnSomme x + poids l x.length := by
  sorry

theorem inversion (l₁ l₂ : List Nat) (a b : Nat) (ha : a < 10) (hb : b < 10)
    (h : isbnSomme (l₁ ++ a :: b :: l₂) % 11 = isbnSomme (l₁ ++ b :: a :: l₂) % 11) : a = b := by
  sorry

end Parcours.Prog

#verifier
