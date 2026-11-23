import Exercices.Probabilites.Definitions

/-!
# Le problème du grand-duc de Toscane

Vers 1620, le grand-duc de Toscane demande à Galilée : avec trois dés, 9 et 10 s'obtiennent
chacun de 6 façons (`9 = 1+2+6 = 1+3+5 = …`), pourtant 10 sort plus souvent que 9. Pourquoi ?
Galilée répond qu'il faut compter les dés **dans l'ordre** : `1+2+6` correspond à 6 lancers
différents, mais `3+3+3` à un seul. Il y a 27 lancers qui font 10, et 25 qui font 9.

## À prouver
1. `six_et_six` : 9 et 10 ont chacun 6 décompositions (sans ordre).
2. `galilee` : la probabilité de 10 est 27/216, celle de 9 est 25/216.

## Ressources
- [Problème du duc de Toscane (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Problem_of_points)

---
*Exercice* `Probabilites.Galilee` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Probabilites.Galilee` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Proba

def troisDes : List (Nat × Nat × Nat) :=
  de.flatMap fun a => de.flatMap fun b => de.map fun c => (a, b, c)

def total (t : Nat × Nat × Nat) : Nat := t.1 + t.2.1 + t.2.2

/-- Les trois dés rangés dans l'ordre croissant. -/
def ranger (t : Nat × Nat × Nat) : Nat × Nat × Nat :=
  let a := t.1
  let b := t.2.1
  let c := t.2.2
  (min a (min b c), a + b + c - min a (min b c) - max a (max b c), max a (max b c))

theorem six_et_six : ((troisDes.filter (total · == 9)).map ranger).eraseDups.length = 6 ∧
    ((troisDes.filter (total · == 10)).map ranger).eraseDups.length = 6 := by
  sorry

theorem galilee : ProbaEst troisDes (total · == 10) 27 216 ∧ ProbaEst troisDes (total · == 9) 25 216 := by
  sorry

end Parcours.Proba

#verifier
