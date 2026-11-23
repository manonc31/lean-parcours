import Exercices.Recurrence.Definitions

/-!
# La fonction d'Ackermann

```
ack 0 n = n + 1
ack (m+1) 0 = ack m 1
ack (m+1) (n+1) = ack m (ack (m+1) n)
```

Elle termine toujours (Lean l'a vérifié avec un ordre **lexicographique** sur `(m, n)`), mais elle
grandit à une vitesse vertigineuse : `ack 4 2` a 19 729 chiffres. C'est l'exemple historique
(1928) d'une fonction calculable qui n'est pas « récursive primitive » (aucune boucle `for` ne suffit).

## À prouver
1. `ack_un : ack 1 n = n + 2`
2. `ack_deux : ack 2 n = 2 * n + 3`
3. `ack_trois : ack 3 n = 2 ^ (n + 3) - 3`
4. `lt_ack : n < ack m n`

## Ressources
- [Fonction d'Ackermann (Wikipédia)](https://fr.wikipedia.org/wiki/Fonction_d%27Ackermann)

---
*Exercice* `Terminaison.Ackermann` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Terminaison.Ackermann` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Term

def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)

theorem ack_un (n : Nat) : ack 1 n = n + 2 := by
  sorry

theorem ack_deux (n : Nat) : ack 2 n = 2 * n + 3 := by
  sorry

theorem ack_trois (n : Nat) : ack 3 n = 2 ^ (n + 3) - 3 := by
  sorry

theorem lt_ack (m n : Nat) : n < ack m n := by
  sorry

end Parcours.Term

#verifier
