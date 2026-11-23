import Exercices.Combinatoire.BinomBase

/-!
# Les nombres de Catalan

Combien de façons d'écrire `n` paires de parenthèses bien équilibrées ? `1, 1, 2, 5, 14, 42…` :
les **nombres de Catalan**. Ils comptent aussi les façons de découper un polygone en triangles,
les chemins de Dyck, les arbres binaires… Ils vérifient `C(n + 1) = Σ C(i) C(n − i)` (on coupe à la
parenthèse qui ferme la première), et `C(n) = binom (2n) n / (n + 1)`.

## À prouver
1. `catalan_compte` : pour `n ≤ 5`, le nombre de mots bien parenthésés de longueur `2n` est `C(n)`.
2. `catalan_binom` : `C(n) × (n + 1) = binom (2n) n` pour `n < 15`.
3. `catalan_dix : catalan 10 = 16796`

## Ressources
- [Nombre de Catalan (Wikipédia)](https://fr.wikipedia.org/wiki/Nombre_de_Catalan)

---
*Exercice* `Combinatoire.Catalan` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Combinatoire.Catalan` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Combi

/-- Tous les mots de `n` lettres `true` (ouvrante) / `false` (fermante). -/
def motsP : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (motsP n).flatMap fun w => [true :: w, false :: w]

def dyck : List Bool → Nat → Bool
  | [], c => c == 0
  | true :: w, c => dyck w (c + 1)
  | false :: w, c => c != 0 && dyck w (c - 1)

/-- La liste `[C(0), …, C(n)]`, calculée par la récurrence. -/
def catalans : Nat → List Nat
  | 0 => [1]
  | n + 1 =>
    let l := catalans n
    l ++ [((List.range (n + 1)).map fun i => l.getD i 0 * l.getD (n - i) 0).sum]

def catalan (n : Nat) : Nat := (catalans n).getD n 0

theorem catalan_compte : ∀ n, n < 6 → ((motsP (2 * n)).filter (dyck · 0)).length = catalan n := by
  sorry

theorem catalan_binom : ∀ n, n < 15 → catalan n * (n + 1) = binom (2 * n) n := by
  sorry

theorem catalan_dix : catalan 10 = 16796 := by
  sorry

end Parcours.Combi

#verifier
