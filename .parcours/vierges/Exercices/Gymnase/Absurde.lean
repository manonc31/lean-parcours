import ParcoursOutils

/-!
# Une égalité absurde

`2 = 3` est faux, et `decide` le sait : `(by decide : (2 : Nat) ≠ 3)`. Avec `absurd h preuve_de_non_h`, on conclut n'importe quoi.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.Absurde` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Gymnase.Absurde` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem absurde (h : (2 : Nat) = 3) : False := by
  sorry

end Parcours.Gymnase

#verifier
