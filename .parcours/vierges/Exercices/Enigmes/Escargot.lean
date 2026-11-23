import Exercices.Recurrence.Definitions

/-!
# L'escargot dans le puits

Un escargot est au fond d'un puits de 10 mètres. Le jour, il monte de 3 mètres ; la nuit, il
glisse de 2 mètres. En combien de jours sort-il ? Pas 10 ! Le 8ᵉ jour, il part de 7 mètres et
atteint le bord avant de glisser.

`jours h f x` simule l'escargot dans un puits de hauteur `h`, parti le matin à la hauteur `x`
(avec au plus `f` jours de simulation).

## À prouver
1. `jours_spec` : dans un puits de `n + 3` mètres, l'escargot parti de `x` sort en `n − x + 1` jours.
2. `escargot : jours 10 8 0 = 8`

---
*Exercice* `Enigmes.Escargot` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Enigmes.Escargot` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Enigmes

def jours (h : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, x => if h ≤ x + 3 then 1 else 1 + jours h f (x + 3 - 2)

theorem jours_spec (n f x : Nat) (hx : x ≤ n) (hf : n - x + 1 ≤ f) :
    jours (n + 3) f x = n - x + 1 := by
  sorry

theorem escargot : jours 10 8 0 = 8 := by
  sorry

end Parcours.Enigmes

#verifier
