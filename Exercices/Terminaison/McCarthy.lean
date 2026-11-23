import Exercices.Recurrence.Definitions

/-!
# La fonction 91 de McCarthy

```
M(n) = n - 10           si n > 100
M(n) = M(M(n + 11))     sinon
```

Une récursion **imbriquée** : l'argument de l'appel extérieur est lui-même un appel récursif !
Surprise : pour tout `n ≤ 100`, `M(n) = 91`. Prouver que ça termine est délicat (ce n'est pas l'argument
qui diminue). On contourne avec du **carburant** : `mc91 f n` fait au plus `f` étapes et rend
`none` s'il manque de carburant. On prouve qu'avec assez de carburant, le résultat est `91`.

## À prouver
1. `mc91_mono : mc91 f n = some v → mc91 (f + k) n = some v`
2. `mc91_spec : n ≤ 100 → ∃ f, mc91 f n = some 91`

## Ressources
- [Fonction 91 de McCarthy (Wikipédia)](https://fr.wikipedia.org/wiki/Fonction_91_de_McCarthy)

---
*Exercice* `Terminaison.McCarthy` · difficulté ★★★★☆

💡 Indices : `./parcours indice Terminaison.McCarthy` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Term

def mc91 : Nat → Nat → Option Nat
  | 0, _ => none
  | f + 1, n => if n > 100 then some (n - 10) else (mc91 f (n + 11)).bind (mc91 f)

theorem mc91_succ (f n : Nat) :
    mc91 (f + 1) n = if n > 100 then some (n - 10) else (mc91 f (n + 11)).bind (mc91 f) := rfl

theorem mc91_mono (f k n v : Nat) (h : mc91 f n = some v) : mc91 (f + k) n = some v := by
  sorry

theorem mc91_spec (n : Nat) (hn : n ≤ 100) : ∃ f, mc91 f n = some 91 := by
  sorry
termination_by 101 - n

end Parcours.Term

#verifier
