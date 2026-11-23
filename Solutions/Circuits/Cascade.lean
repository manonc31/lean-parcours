/- @parcours
titre: L'additionneur en cascade
difficulte: 3
indice: `fun_induction ajouter a b c with` : quatre cas (les deux listes vides, une seule vide, aucune).
indice: Dans chaque cas récursif : `simp only [valeur_cons, …]`, l'hypothèse de récurrence, et l'égalité `additionneur_complet` pour les trois bits du rang courant. Puis `omega` (avec les `toNat` comme inconnues).
-/
import Solutions.Circuits.Additionneurs

/-!
# L'additionneur en cascade

Pour additionner deux nombres de `n` bits, on enchaîne `n` additionneurs complets : la retenue
de chacun entre dans le suivant (*ripple-carry adder*). C'est ce que fait un processeur.
Ici les deux nombres peuvent avoir des longueurs différentes (les bits manquants valent 0).

## À prouver
`ajouter_correct : valeur (ajouter a b c) = valeur a + valeur b + c.toNat`
-/

namespace Parcours.Circuits

def ajouter : List Bool → List Bool → Bool → List Bool
  | [], [], c => [c]
  | x :: a, [], c => somme x false c :: ajouter a [] (retenue x false c)
  | [], y :: b, c => somme false y c :: ajouter [] b (retenue false y c)
  | x :: a, y :: b, c => somme x y c :: ajouter a b (retenue x y c)

theorem ajouter_correct (a b : List Bool) (c : Bool) :
    valeur (ajouter a b c) = valeur a + valeur b + c.toNat := by -- @exo
  fun_induction ajouter a b c with
  | case1 c =>
    simp only [valeur_cons, valeur_nil]
    omega
  | case2 x a c ih =>
    have h := additionneur_complet x false c
    simp only [valeur_cons, valeur_nil, ih] at h ⊢
    simp only [Bool.toNat_false] at h
    omega
  | case3 y b c ih =>
    have h := additionneur_complet false y c
    simp only [valeur_cons, valeur_nil, ih] at h ⊢
    simp only [Bool.toNat_false] at h
    omega
  | case4 x a y b c ih =>
    have h := additionneur_complet x y c
    simp only [valeur_cons, ih]
    omega

end Parcours.Circuits

#verifier
