import Exercices.Combinatoire.BinomBase

/-!
# Combien de poignées de main ?

Dans un groupe de `n` personnes, si chacun serre la main de chacun, il y a `C(n, 2) = n(n−1)/2` poignées
de main. Sans division : `2 × C(n, 2) = n(n − 1)`.

## À prouver
`deux_parmi (n : Nat) : 2 * binom n 2 = n * (n - 1)`

---
*Exercice* `Combinatoire.DeuxParmi` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Combinatoire.DeuxParmi` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Combi

theorem deux_parmi (n : Nat) : 2 * binom n 2 = n * (n - 1) := by
  sorry

end Parcours.Combi

#verifier
