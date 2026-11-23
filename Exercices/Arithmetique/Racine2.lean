import Exercices.Arithmetique.Definitions

/-!
# √2 est irrationnel

Si `√2 = a/b`, alors `a² = 2b²`. On montre que c'est impossible (avec `b > 0`), par la
**descente infinie** de Fermat : toute solution en donnerait une plus petite, à l'infini…
ce qui est impossible dans ℕ (c'est une récurrence forte déguisée).

## À prouver
`racine_deux_irrationnelle : ¬∃ a b : Nat, 0 < b ∧ a * a = 2 * (b * b)`

## Ressources
- [Racine carrée de deux (Wikipédia)](https://fr.wikipedia.org/wiki/Racine_carr%C3%A9e_de_deux)

---
*Exercice* `Arithmetique.Racine2` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Arithmetique.Racine2` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Arith

theorem racine_deux_irrationnelle : ¬∃ a b : Nat, 0 < b ∧ a * a = 2 * (b * b) := by
  sorry

end Parcours.Arith

#verifier
