import Exercices.Arithmetique.Definitions

/-!
# Moyenne arithmétique et géométrique

L'inégalité **arithmético-géométrique** : `√(ab) ≤ (a + b)/2`. Sans racine : `4ab ≤ (a + b)²`.
C'est l'inégalité la plus utilisée des olympiades. (Numéro 38 de la liste des « 100 théorèmes »,
dans sa version à deux nombres.)

## À prouver
`amgm (a b : Nat) : 4 * a * b ≤ (a + b) ^ 2`

## Ressources
- [Inégalité arithmético-géométrique (Wikipédia)](https://fr.wikipedia.org/wiki/In%C3%A9galit%C3%A9_arithm%C3%A9tico-g%C3%A9om%C3%A9trique)

---
*Exercice* `Olympiades.AMGM` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Olympiades.AMGM` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Olymp

theorem amgm (a b : Nat) : 4 * a * b ≤ (a + b) ^ 2 := by
  sorry

end Parcours.Olymp

#verifier
