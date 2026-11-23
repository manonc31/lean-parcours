/- @parcours
titre: Les arbres binaires de recherche
difficulte: 4
indice: Toutes les preuves : récurrence sur l'arbre (`induction t with | vide => … | noeud g x d ihg ihd => …`), `simp only [inserer, chercher, …]`, et `split` pour les `if`.
indice: Dans le cas « ni `y < x` ni `x < y` », on a `y = x` (`omega`). Pour les équivalences entre « ou » qui restent, `grind` fait le raisonnement logique.
indice: `chercher_correct` : si `y < x`, `y` ne peut pas être dans `d` (tous ses éléments sont `> x`) : utilise `tous_contient`.
-/
import Solutions.Algorithmes.Definitions

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
    (inserer y t).contient z ↔ z = y ∨ t.contient z := by -- @exo
  induction t with
  | vide => simp [inserer, Arbre.contient]
  | noeud g x d ihg ihd =>
    simp only [inserer]
    split
    · simp only [Arbre.contient, ihg]
      grind
    · split
      · simp only [Arbre.contient, ihd]
        grind
      · simp only [Arbre.contient]
        grind

theorem tous_contient {p : Nat → Prop} {t : Arbre} (h : t.tous p) {z : Nat} (hz : t.contient z) : p z := by -- @exo
  induction t with
  | vide => exact hz.elim
  | noeud g x d ihg ihd =>
    obtain ⟨hx, hg, hd⟩ := h
    rcases hz with rfl | hz | hz
    · exact hx
    · exact ihg hg hz
    · exact ihd hd hz

theorem tous_inserer {p : Nat → Prop} {t : Arbre} (h : t.tous p) {y : Nat} (hy : p y) :
    (inserer y t).tous p := by -- @exo
  induction t with
  | vide => exact ⟨hy, trivial, trivial⟩
  | noeud g x d ihg ihd =>
    obtain ⟨hx, hg, hd⟩ := h
    simp only [inserer]
    split
    · exact ⟨hx, ihg hg, hd⟩
    · split
      · exact ⟨hx, hg, ihd hd⟩
      · exact ⟨hx, hg, hd⟩

theorem inserer_abr {t : Arbre} (h : ABR t) (y : Nat) : ABR (inserer y t) := by -- @exo
  induction t with
  | vide => exact ⟨trivial, trivial, trivial, trivial⟩
  | noeud g x d ihg ihd =>
    obtain ⟨hg, hd, ag, ad⟩ := h
    simp only [inserer]
    split
    · exact ⟨tous_inserer hg ‹_›, hd, ihg ag, ad⟩
    · split
      · exact ⟨hg, tous_inserer hd ‹_›, ag, ihd ad⟩
      · exact ⟨hg, hd, ag, ad⟩

theorem chercher_correct {t : Arbre} (h : ABR t) (y : Nat) : chercher y t = true ↔ t.contient y := by -- @exo
  induction t with
  | vide => simp [chercher, Arbre.contient]
  | noeud g x d ihg ihd =>
    obtain ⟨hg, hd, ag, ad⟩ := h
    simp only [chercher, Arbre.contient]
    split
    · rw [ihg ag]
      constructor
      · intro hy
        exact Or.inr (Or.inl hy)
      · rintro (rfl | hy | hy)
        · omega
        · exact hy
        · have := tous_contient hd hy
          omega
    · split
      · rw [ihd ad]
        constructor
        · intro hy
          exact Or.inr (Or.inr hy)
        · rintro (rfl | hy | hy)
          · omega
          · have := tous_contient hg hy
            omega
          · exact hy
      · simp only [true_iff]
        left
        omega

end Parcours.Algo

#verifier
