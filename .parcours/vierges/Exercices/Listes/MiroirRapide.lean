import Exercices.Listes.Miroir

/-!
# Un miroir rapide

Le `miroir` naïf est **lent** : pour chaque élément il refait une concaténation, ce qui coûte
un temps quadratique. La version « avec accumulateur » est linéaire :

```
miroirAcc nil acc = acc
miroirAcc (x ∷ l) acc = miroirAcc l (x ∷ acc)
```

Optimiser un programme, c'est bien. **Prouver** que l'optimisation donne le même résultat, c'est mieux.

## À prouver
1. `miroirAcc_spec (l acc : Liste α) : miroirAcc l acc = miroir l ++ acc`
2. `miroirRapide_eq (l : Liste α) : miroirRapide l = miroir l`

---
*Exercice* `Listes.MiroirRapide` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Listes.MiroirRapide` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Listes.Liste

variable {α : Type}

def miroirAcc : Liste α → Liste α → Liste α
  | nil, acc => acc
  | x ∷ l, acc => miroirAcc l (x ∷ acc)

def miroirRapide (l : Liste α) : Liste α := miroirAcc l nil

theorem miroirAcc_spec (l acc : Liste α) : miroirAcc l acc = miroir l ++ acc := by
  sorry

theorem miroirRapide_eq (l : Liste α) : miroirRapide l = miroir l := by
  sorry

end Parcours.Listes.Liste

#verifier
