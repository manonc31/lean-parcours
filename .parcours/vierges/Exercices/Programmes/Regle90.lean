import Exercices.Programmes.Definitions
import Exercices.Programmes.Pascal

/-!
# La règle 90 et le triangle de Sierpiński

Un **automate cellulaire** sur une ligne : chaque case devient vivante si exactement une de ses
deux voisines l'était (OU exclusif). En partant d'une seule case vivante, on voit apparaître le
**triangle de Sierpiński**… qui n'est autre que le triangle de Pascal **modulo 2** !
```
        █
       █ █
      █   █
     █ █ █ █
    █       █
```

## À prouver
`sierpinski` : pour les 16 premières lignes, la règle 90 donne le triangle de Pascal modulo 2
(avec une case vide entre deux coefficients).

## Ressources
- [Règle 90 (Wikipédia)](https://fr.wikipedia.org/wiki/R%C3%A8gle_90)

---
*Exercice* `Programmes.Regle90` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Programmes.Regle90` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

/-- Une génération : la ligne s'allonge d'une case de chaque côté. -/
def regle90 (l : List Bool) : List Bool := List.zipWith (· ^^ ·) (false :: false :: l) (l ++ [false, false])

/-- `[a, b, c]` ↦ `[a, false, b, false, c]` -/
def intercaler : List Bool → List Bool
  | [] => []
  | [a] => [a]
  | a :: r => a :: false :: intercaler r

theorem sierpinski : ∀ n, n < 16 →
    repeter regle90 n [true] = intercaler ((pascal n).map (· % 2 == 1)) := by
  sorry

end Parcours.Prog

#verifier
