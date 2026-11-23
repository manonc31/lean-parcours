import Exercices.Combinatoire.BinomBase

/-!
# Chemins dans une grille

Combien de chemins pour aller du coin `(0, 0)` au coin `(m, n)` d'une grille, en ne faisant que des pas
vers la droite ou vers le haut ? `chemins m n` les compte récursivement (le dernier pas vient de la gauche
ou d'en bas). La réponse : `C(m + n, m)`, on choisit les positions des `m` pas vers la droite.

## À prouver
`chemins_binom (m n : Nat) : chemins m n = binom (m + n) m`

---
*Exercice* `Combinatoire.Chemins` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Combinatoire.Chemins` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Combi

def chemins : Nat → Nat → Nat
  | 0, _ => 1
  | _, 0 => 1
  | m + 1, n + 1 => chemins m (n + 1) + chemins (m + 1) n

theorem chemins_binom (m n : Nat) : chemins m n = binom (m + n) m := by
  sorry

end Parcours.Combi

#verifier
