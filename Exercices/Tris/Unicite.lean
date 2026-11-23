import Exercices.Tris.Definitions

/-!
# Il n'y a qu'une façon d'être trié

Deux listes triées qui sont permutation l'une de l'autre sont **égales**.
Conséquence : tous les algorithmes de tri corrects donnent **exactement** le même résultat.

## À prouver
`trie_unique : Trie l₁ → Trie l₂ → l₁.Perm l₂ → l₁ = l₂`

---
*Exercice* `Tris.Unicite` · difficulté ★★★★☆

💡 Indices : `./parcours indice Tris.Unicite` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Tris

theorem trie_unique (l₁ l₂ : List Nat) (h₁ : Trie l₁) (h₂ : Trie l₂) (hp : l₁.Perm l₂) :
    l₁ = l₂ := by
  sorry

end Parcours.Tris

#verifier
