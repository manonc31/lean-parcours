import Exercices.Circuits.Additionneurs

/-!
# L'additionneur en cascade

Pour additionner deux nombres de `n` bits, on enchaîne `n` additionneurs complets : la retenue
de chacun entre dans le suivant (*ripple-carry adder*). C'est ce que fait un processeur.
Ici les deux nombres peuvent avoir des longueurs différentes (les bits manquants valent 0).

## À prouver
`ajouter_correct : valeur (ajouter a b c) = valeur a + valeur b + c.toNat`

---
*Exercice* `Circuits.Cascade` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Circuits.Cascade` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Circuits

def ajouter : List Bool → List Bool → Bool → List Bool
  | [], [], c => [c]
  | x :: a, [], c => somme x false c :: ajouter a [] (retenue x false c)
  | [], y :: b, c => somme false y c :: ajouter [] b (retenue false y c)
  | x :: a, y :: b, c => somme x y c :: ajouter a b (retenue x y c)

theorem ajouter_correct (a b : List Bool) (c : Bool) :
    valeur (ajouter a b c) = valeur a + valeur b + c.toNat := by
  sorry

end Parcours.Circuits

#verifier
