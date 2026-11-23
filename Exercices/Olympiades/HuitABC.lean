import Exercices.Classiques.CauchySchwarz

/-!
# (a + b)(b + c)(c + a) ≥ 8abc

Pour `a, b, c ≥ 0` : `(a + b)(b + c)(c + a) ≥ 8abc`. On peut le voir avec AM-GM
(`a + b ≥ 2√ab`…), mais il y a plus simple : la différence vaut
`a(b − c)² + b(c − a)² + c(a − b)²`, une somme de termes positifs.

## À prouver
`huit_abc : 0 ≤ a → 0 ≤ b → 0 ≤ c → 8 * a * b * c ≤ (a + b) * (b + c) * (c + a)`

---
*Exercice* `Olympiades.HuitABC` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Olympiades.HuitABC` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Olymp

theorem huit_abc (a b c : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    8 * a * b * c ≤ (a + b) * (b + c) * (c + a) := by
  sorry

end Parcours.Olymp

#verifier
