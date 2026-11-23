import Exercices.Programmes.Definitions

/-!
# Supprimer les doublons

`dedup` garde un seul exemplaire de chaque élément (le dernier).

## À prouver
1. `mem_dedup : x ∈ dedup l ↔ x ∈ l` (on n'a rien perdu)
2. `nodup_dedup : (dedup l).Nodup` (plus aucun doublon)

---
*Exercice* `Programmes.Dedoublonner` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Programmes.Dedoublonner` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

def dedup : List Nat → List Nat
  | [] => []
  | x :: l => if x ∈ l then dedup l else x :: dedup l

theorem mem_dedup (x : Nat) (l : List Nat) : x ∈ dedup l ↔ x ∈ l := by
  sorry

theorem nodup_dedup (l : List Nat) : (dedup l).Nodup := by
  sorry

end Parcours.Prog

#verifier
