import Exercices.Classiques.CauchySchwarz

/-!
# L'inégalité du réordonnement

## Se le représenter
Tu dois acheter `a` objets à un prix et `b` à un autre, avec `a ≤ b`, et tu peux choisir les prix
parmi `c ≤ d`. Pour payer le plus, on met le plus gros prix sur la plus grosse quantité :
`a·c + b·d ≥ a·d + b·c`. Visuellement : la différence est l'aire du rectangle `(b − a) × (d − c)`.

## À prouver
`reordonnement : a ≤ b → c ≤ d → a * d + b * c ≤ a * c + b * d`

## Ressources
- [Inégalité de réarrangement (Wikipédia)](https://fr.wikipedia.org/wiki/In%C3%A9galit%C3%A9_de_r%C3%A9arrangement)

---
*Exercice* `Classiques.Reordonnement` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Classiques.Reordonnement` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Classiques

theorem reordonnement (a b c d : Int) (h1 : a ≤ b) (h2 : c ≤ d) :
    a * d + b * c ≤ a * c + b * d := by
  sorry

end Parcours.Classiques

#verifier
