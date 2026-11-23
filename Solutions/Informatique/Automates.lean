/- @parcours
titre: Les automates finis
difficulte: 3
indice: `lire_produit` : récurrence sur `w` en généralisant `p` et `q` (`induction w generalizing p q`). Le cas `a :: w` : `simp only [Automate.lire]` puis `ih`.
indice: `produit_correct` : `unfold Automate.accepte`, puis `rw [lire_produit]`, puis `rfl`.
indice: `pair_correct` : prouve un lemme plus général `∀ e, pairB.lire e w = (e == (compte w % 2 == 1))`… ou plus simple : `pairB.lire e w = xor e (impair w)` où `impair` se calcule par récurrence. Choisis bien l'énoncé généralisé !
-/
import Solutions.Informatique.Expressions

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
    (produit A B).lire (p, q) w = (A.lire p w, B.lire q w) := by -- @exo
  induction w generalizing p q with
  | nil => rfl
  | cons a w ih =>
    simp only [Automate.lire]
    exact ih _ _

theorem produit_correct (A : Automate σ α) (B : Automate τ α) (w : List α) :
    (produit A B).accepte w = (A.accepte w && B.accepte w) := by -- @exo
  unfold Automate.accepte
  rw [show (produit A B).init = (A.init, B.init) from rfl, lire_produit]
  rfl

theorem complement_correct (A : Automate σ α) (w : List α) :
    (complement A).accepte w = !A.accepte w := by -- @exo
  have h : ∀ e, (complement A).lire e w = A.lire e w := by
    induction w with
    | nil => intro e; rfl
    | cons a w ih => intro e; exact ih _
  unfold Automate.accepte
  rw [show (complement A).init = A.init from rfl, h]
  rfl

/-- `impair w` : le nombre de `true` dans `w` est impair. -/
def impair : List Bool → Bool
  | [] => false
  | b :: w => xor b (impair w)

/-- L'état `e` vaut « on a lu un nombre impair de `true` jusqu'ici ». -/
def pairB : Automate Bool Bool := ⟨false, fun e a => xor e a, fun e => !e⟩

theorem pair_correct (w : List Bool) : pairB.accepte w = !impair w := by -- @exo
  have h : ∀ e, pairB.lire e w = xor e (impair w) := by
    induction w with
    | nil => intro e; cases e <;> rfl
    | cons a w ih =>
      intro e
      simp only [Automate.lire, impair]
      rw [ih]
      show xor (xor e a) (impair w) = xor e (xor a (impair w))
      cases e <;> cases a <;> cases impair w <;> rfl
  unfold Automate.accepte
  rw [show pairB.init = false from rfl, h]
  cases impair w <;> rfl

end Parcours.Info

#verifier
