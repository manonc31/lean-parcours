import Exercices.Programmes.Definitions

/-!
# Le crible d'Ératosthène

Pour trouver les nombres premiers jusqu'à 100 (Ératosthène, IIIᵉ siècle av. J.-C.) : écris les
nombres à partir de 2 ; le premier, 2, est premier, raye tous ses multiples ; le suivant non
rayé, 3, est premier, raye ses multiples ; et ainsi de suite.

## À prouver
1. `crible_sous_liste` : le crible ne garde que des nombres de la liste de départ.
2. `vingt_cinq` : il y a 25 nombres premiers inférieurs à 100.
3. `crible_ok` : le crible trouve exactement les nombres qui n'ont pas de diviseur entre 2 et `n − 1`.

## Ressources
- [Crible d'Ératosthène (Wikipédia)](https://fr.wikipedia.org/wiki/Crible_d%27%C3%89ratosth%C3%A8ne)

---
*Exercice* `Programmes.Crible` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Programmes.Crible` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

/-- `f` est une réserve de calcul (le nombre d'étapes maximum). -/
def crible : Nat → List Nat → List Nat
  | 0, _ => []
  | _, [] => []
  | f + 1, p :: l => p :: crible f (l.filter (· % p != 0))

def premiersJusqua (n : Nat) : List Nat := crible n (List.range' 2 (n - 2))

theorem crible_sous_liste (f : Nat) (l : List Nat) : ∀ x ∈ crible f l, x ∈ l := by
  sorry

theorem vingt_cinq : (premiersJusqua 100).length = 25 := by
  sorry

theorem crible_ok : premiersJusqua 100 = (List.range 100).filter fun n =>
    2 ≤ n && (List.range n).all fun d => d < 2 || n % d != 0 := by
  sorry

end Parcours.Prog

#verifier
