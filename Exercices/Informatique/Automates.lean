import Exercices.Informatique.Expressions

/-!
# Les automates finis

Un **automate** lit un mot lettre par lettre en changeant d'état ; à la fin, il accepte ou rejette.
Ce sont les machines derrière les expressions régulières, les analyseurs lexicaux, les protocoles…

## À prouver
1. `lire_produit` et `produit_correct` : l'automate **produit** reconnaît l'**intersection** des langages.
2. `complement_correct` : en inversant les états acceptants, on reconnaît le **complémentaire**.
3. `pair_correct` : un automate à 2 états qui reconnaît les mots ayant un nombre **pair** de `true`.

## Ressources
- [Automate fini (Wikipédia)](https://fr.wikipedia.org/wiki/Automate_fini)

---
*Exercice* `Informatique.Automates` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Informatique.Automates` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Info

structure Automate (σ α : Type) where
  init : σ
  trans : σ → α → σ
  accept : σ → Bool

variable {σ τ α : Type}

def Automate.lire (A : Automate σ α) : σ → List α → σ
  | e, [] => e
  | e, a :: w => A.lire (A.trans e a) w

def Automate.accepte (A : Automate σ α) (w : List α) : Bool := A.accept (A.lire A.init w)

def produit (A : Automate σ α) (B : Automate τ α) : Automate (σ × τ) α :=
  ⟨(A.init, B.init), fun e a => (A.trans e.1 a, B.trans e.2 a), fun e => A.accept e.1 && B.accept e.2⟩

def complement (A : Automate σ α) : Automate σ α := ⟨A.init, A.trans, fun e => !A.accept e⟩

theorem lire_produit (A : Automate σ α) (B : Automate τ α) (p : σ) (q : τ) (w : List α) :
    (produit A B).lire (p, q) w = (A.lire p w, B.lire q w) := by
  sorry

theorem produit_correct (A : Automate σ α) (B : Automate τ α) (w : List α) :
    (produit A B).accepte w = (A.accepte w && B.accepte w) := by
  sorry

theorem complement_correct (A : Automate σ α) (w : List α) :
    (complement A).accepte w = !A.accepte w := by
  sorry

/-- `impair w` : le nombre de `true` dans `w` est impair. -/
def impair : List Bool → Bool
  | [] => false
  | b :: w => xor b (impair w)

/-- L'état `e` vaut « on a lu un nombre impair de `true` jusqu'ici ». -/
def pairB : Automate Bool Bool := ⟨false, fun e a => xor e a, fun e => !e⟩

theorem pair_correct (w : List Bool) : pairB.accepte w = !impair w := by
  sorry

end Parcours.Info

#verifier
