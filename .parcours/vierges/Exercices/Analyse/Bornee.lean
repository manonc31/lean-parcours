import Exercices.Analyse.ValeurAbsolue

/-!
# Toute suite convergente est bornée

Si `u` converge, il existe `M` tel que `|u n| ≤ M` pour tout `n`. L'idée : après un certain rang,
les termes sont proches de la limite ; avant, il n'y en a qu'un nombre fini.

## À prouver
`convergente_bornee : Tend u l → ∃ M, ∀ n, vabs (u n) ≤ M`

---
*Exercice* `Analyse.Bornee` · difficulté ★★★★☆

💡 Indices : `./parcours indice Analyse.Bornee` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Analyse

theorem convergente_bornee {u : Suite} {l : Rat} (h : Tend u l) : ∃ M, ∀ n, vabs (u n) ≤ M := by
  sorry

end Parcours.Analyse

#verifier
