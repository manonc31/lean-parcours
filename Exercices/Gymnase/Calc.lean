import ParcoursOutils

/-!
# Raisonner par étapes avec calc

`calc` permet d'écrire une preuve comme au tableau :

```
calc a = b + 1 := h1
  _ = 2 + 1 := by rw [h2]
  _ = 3 := rfl
```
Chaque ligne `_ = …` continue la chaîne, avec sa justification après `:=`.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.Calc` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Gymnase.Calc` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem calc_exemple (a b : Nat) (h1 : a = b + 1) (h2 : b = 2) : a = 3 := by
  sorry

end Parcours.Gymnase

#verifier
