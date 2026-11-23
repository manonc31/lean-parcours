import Exercices.Algorithmes.Definitions

/-!
# Les arbres binaires de recherche

Un **ABR** stocke des nombres dans un arbre : à chaque nœud `x`, tout ce qui est à gauche est
`< x`, tout ce qui est à droite est `> x`. Chercher ou insérer prend un temps proportionnel à la
hauteur de l'arbre (au lieu de la taille). C'est la structure derrière les dictionnaires et les
index de bases de données.

## À prouver
1. `contient_inserer` : après insertion de `y`, l'arbre contient `y` et tout ce qu'il contenait (et rien d'autre).
2. `tous_contient` : si tous les éléments vérifient `p`, et `z` est dans l'arbre, alors `p z`.
3. `inserer_abr` : l'insertion préserve la propriété d'ABR.
4. `chercher_correct` : dans un ABR, `chercher` répond juste.

## Ressources
- [Arbre binaire de recherche (Wikipédia)](https://fr.wikipedia.org/wiki/Arbre_binaire_de_recherche)

---
*Exercice* `Algorithmes.ABR` · difficulté ★★★★☆

💡 Indices : `./parcours indice Algorithmes.ABR` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Algo

inductive Arbre where
  | vide
  | noeud (g : Arbre) (x : Nat) (d : Arbre)

open Arbre

def Arbre.contient : Arbre → Nat → Prop
  | vide, _ => False
  | noeud g x d, y => y = x ∨ g.contient y ∨ d.contient y

def Arbre.tous (p : Nat → Prop) : Arbre → Prop
  | vide => True
  | noeud g x d => p x ∧ g.tous p ∧ d.tous p

def ABR : Arbre → Prop
  | vide => True
  | noeud g x d => g.tous (· < x) ∧ d.tous (x < ·) ∧ ABR g ∧ ABR d

def inserer (y : Nat) : Arbre → Arbre
  | vide => noeud vide y vide
  | noeud g x d => if y < x then noeud (inserer y g) x d
    else if x < y then noeud g x (inserer y d) else noeud g x d

def chercher (y : Nat) : Arbre → Bool
  | vide => false
  | noeud g x d => if y < x then chercher y g else if x < y then chercher y d else true

theorem contient_inserer (y z : Nat) (t : Arbre) :
    (inserer y t).contient z ↔ z = y ∨ t.contient z := by
  sorry

theorem tous_contient {p : Nat → Prop} {t : Arbre} (h : t.tous p) {z : Nat} (hz : t.contient z) : p z := by
  sorry

theorem tous_inserer {p : Nat → Prop} {t : Arbre} (h : t.tous p) {y : Nat} (hy : p y) :
    (inserer y t).tous p := by
  sorry

theorem inserer_abr {t : Arbre} (h : ABR t) (y : Nat) : ABR (inserer y t) := by
  sorry

theorem chercher_correct {t : Arbre} (h : ABR t) (y : Nat) : chercher y t = true ↔ t.contient y := by
  sorry

end Parcours.Algo

#verifier
