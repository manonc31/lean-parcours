import Exercices.Probabilites.Definitions

/-!
# Les boîtes de Bertrand

Trois boîtes : l'une contient deux pièces d'or, l'autre deux pièces d'argent, la troisième une de
chaque. On choisit une boîte au hasard, on en tire une pièce : elle est en or. Quelle est la
probabilité que l'autre pièce de la boîte soit aussi en or ? Pas 1/2, mais **2/3** !
(Joseph Bertrand, 1889.) Raison : on a plus de chances d'avoir tiré de l'or dans la boîte or-or.

On code un tirage par `(boîte, pièce)`, avec 6 tirages équiprobables, puis on ne garde que ceux où
la pièce tirée est en or.

## À prouver
1. `bertrand` : la probabilité vaut 2/3,
2. `pas_un_demi` : et pas 1/2.

## Ressources
- [Paradoxe des boîtes de Bertrand (Wikipédia)](https://fr.wikipedia.org/wiki/Paradoxe_des_bo%C3%AEtes_de_Bertrand)

---
*Exercice* `Probabilites.Bertrand` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Probabilites.Bertrand` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Proba

/-- `true` = or. Boîte 0 : or-or, boîte 1 : or-argent, boîte 2 : argent-argent. -/
def boites : List (List Bool) := [[true, true], [true, false], [false, false]]

def tirages : List (Nat × Nat) := [0, 1, 2].flatMap fun b => [0, 1].map fun p => (b, p)

def orTire (t : Nat × Nat) : Bool := (boites.getD t.1 []).getD t.2 false
def autreOr (t : Nat × Nat) : Bool := (boites.getD t.1 []).getD (1 - t.2) false

theorem bertrand : ProbaEst (tirages.filter orTire) autreOr 2 3 := by
  sorry

theorem pas_un_demi : ¬ ProbaEst (tirages.filter orTire) autreOr 1 2 := by
  sorry

end Parcours.Proba

#verifier
