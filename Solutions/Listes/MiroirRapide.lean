/- @parcours
titre: Un miroir rapide
difficulte: 3
indice: `miroirAcc_spec` doit être prouvé pour TOUT accumulateur : `induction l generalizing acc with`.
indice: Cas `cons x l ih` : `miroirAcc (x ∷ l) acc = miroirAcc l (x ∷ acc)` par définition. Utilise `ih (x ∷ acc)`, puis `miroir_cons` et `concat_assoc`.
indice: `miroirRapide_eq` : `miroirRapide l = miroirAcc l nil`, puis `miroirAcc_spec` et `concat_nil`.
-/
import Solutions.Listes.Miroir

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
-/

namespace Parcours.Listes.Liste

variable {α : Type}

def miroirAcc : Liste α → Liste α → Liste α
  | nil, acc => acc
  | x ∷ l, acc => miroirAcc l (x ∷ acc)

def miroirRapide (l : Liste α) : Liste α := miroirAcc l nil

theorem miroirAcc_spec (l acc : Liste α) : miroirAcc l acc = miroir l ++ acc := by -- @exo
  induction l generalizing acc with
  | nil => rfl
  | cons x l ih =>
    show miroirAcc l (x ∷ acc) = _
    rw [ih, miroir_cons, concat_assoc]
    rfl

theorem miroirRapide_eq (l : Liste α) : miroirRapide l = miroir l := by -- @exo
  show miroirAcc l nil = _
  rw [miroirAcc_spec, concat_nil]

end Parcours.Listes.Liste

#verifier
