import Exercices.Combinatoire.Definitions

/-!
# Le principe des tiroirs

> Si on range `n + 1` chaussettes dans `n` tiroirs, un tiroir contient au moins deux chaussettes.

Version « liste » : une liste **sans doublon** dont tous les éléments sont `< n` a au plus `n` éléments.
Conséquence amusante : parmi 13 personnes, deux sont nées le même mois.

## À prouver
1. `tiroirs : l.Nodup → (∀ x ∈ l, x < n) → l.length ≤ n`
2. `treize_personnes (mois : Fin 13 → Fin 12) : ∃ i j, i ≠ j ∧ mois i = mois j`

## Ressources
- [Principe des tiroirs (Wikipédia)](https://fr.wikipedia.org/wiki/Principe_des_tiroirs)

---
*Exercice* `Combinatoire.Tiroirs` · difficulté ★★★★☆

💡 Indices : `./parcours indice Combinatoire.Tiroirs` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Combi

theorem tiroirs {n : Nat} {l : List Nat} (hnd : l.Nodup) (h : ∀ x ∈ l, x < n) : l.length ≤ n := by
  sorry

theorem treize_personnes (mois : Fin 13 → Fin 12) : ∃ i j, i ≠ j ∧ mois i = mois j := by
  sorry

end Parcours.Combi

#verifier
