import Exercices.Recurrence.Definitions

/-!
# Les pages du livre

Pour numéroter les pages d'un livre (à partir de 1), un imprimeur a utilisé 1 095 chiffres.
Combien de pages a le livre ?

## Se le représenter
Pages 1 à 9 : 9 chiffres. Pages 10 à 99 : `90 × 2 = 180` chiffres. Ensuite, 3 chiffres par page :
`1095 − 189 = 906 = 3 × 302`. Donc `99 + 302 = 401` pages.

## À prouver
1. `croissant : chiffresLivre m ≤ chiffresLivre (m + k)`
2. `formule : chiffresLivre (99 + k) = 189 + 3k` (pour `k ≤ 900`)
3. `livre : chiffresLivre n = 1095 ↔ n = 401` (pour `n ≤ 999`)

---
*Exercice* `Enigmes.PagesLivre` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Enigmes.PagesLivre` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Enigmes

def chiffresPage (p : Nat) : Nat := if p < 10 then 1 else if p < 100 then 2 else 3

def chiffresLivre : Nat → Nat
  | 0 => 0
  | n + 1 => chiffresLivre n + chiffresPage (n + 1)

theorem croissant (m k : Nat) : chiffresLivre m ≤ chiffresLivre (m + k) := by
  sorry

theorem formule (k : Nat) (hk : k ≤ 900) : chiffresLivre (99 + k) = 189 + 3 * k := by
  sorry

theorem livre (n : Nat) (hn : n ≤ 999) : chiffresLivre n = 1095 ↔ n = 401 := by
  sorry

end Parcours.Enigmes

#verifier
