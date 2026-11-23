import Exercices.Combinatoire.Definitions

/-!
# Le cadenas à 4 chiffres

Un cadenas a 4 molettes de 0 à 9 : `10⁴ = 10 000` codes. Combien ont 4 chiffres **tous
différents** ? `10 × 9 × 8 × 7 = 5040` (10 choix pour le premier, 9 pour le second…).
Donc près de la moitié des codes ont un chiffre répété !

## À prouver
1. `differents : 5040` codes à chiffres distincts,
2. `repetes : 4960` codes avec au moins un chiffre répété.

---
*Exercice* `Combinatoire.Cadenas` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Combinatoire.Cadenas` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Combi

def chiffres4 (n : Nat) : List Nat := [n / 1000 % 10, n / 100 % 10, n / 10 % 10, n % 10]

theorem differents :
    ((List.range 10000).filter fun n => (chiffres4 n).eraseDups.length == 4).length = 5040 := by
  sorry

theorem repetes :
    ((List.range 10000).filter fun n => (chiffres4 n).eraseDups.length != 4).length = 4960 := by
  sorry

end Parcours.Combi

#verifier
