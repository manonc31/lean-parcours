/- @parcours
titre: Les opérations sur ℤ
difficulte: 3
indice: Chaque preuve de compatibilité est un calcul sur les naturels avec deux hypothèses. Pour `+` et `-`, `omega` suffit.
indice: Pour `×`, c'est non linéaire : `grind` (le jeton `anneau` est débloqué) sait combiner les hypothèses.
indice: Si `grind` échoue, prouve-le en deux étapes : change d'abord `(a, b)` en `(a', b')` (le second argument fixé), puis `(c, d)` en `(c', d')`.
-/
import Solutions.Constructions.Entiers

/-!
# Les opérations sur ℤ

Sur les couples :
- addition : `(a, b) + (c, d) = (a + c, b + d)`      (car `(a-b) + (c-d) = (a+c) - (b+d)`)
- opposé : `-(a, b) = (b, a)`
- multiplication : `(a, b) × (c, d) = (ac + bd, ad + bc)`  (développe `(a-b)(c-d)` !)

Pour que ces opérations passent au quotient, il faut prouver qu'elles **respectent** `~` :
si on remplace un couple par un couple équivalent, le résultat reste équivalent.
Ces trois lemmes sont utilisés juste en dessous pour définir `+`, `-`, `*` sur `Zr`.

## À prouver
1. `add_respecte`
2. `neg_respecte`
3. `mul_respecte`
-/

namespace Parcours.Constructions

theorem add_respecte {a b c d a' b' c' d' : Nat} (h1 : a + b' = a' + b) (h2 : c + d' = c' + d) :
    (a + c) + (b' + d') = (a' + c') + (b + d) := by -- @exo
  omega

theorem neg_respecte {a b a' b' : Nat} (h : a + b' = a' + b) : b + a' = b' + a := by -- @exo
  omega

theorem mul_respecte {a b c d a' b' c' d' : Nat} (h1 : a + b' = a' + b) (h2 : c + d' = c' + d) :
    (a * c + b * d) + (a' * d' + b' * c') = (a' * c' + b' * d') + (a * d + b * c) := by -- @exo
  grind

def Zr.add : Zr → Zr → Zr :=
  Quotient.lift₂ (fun p q => Zr.mk (p.1 + q.1) (p.2 + q.2))
    (fun ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ h1 h2 => Zr.mk_eq_mk.mpr (add_respecte h1 h2))

def Zr.neg : Zr → Zr :=
  Quotient.lift (fun p => Zr.mk p.2 p.1)
    (fun ⟨_, _⟩ ⟨_, _⟩ h => Zr.mk_eq_mk.mpr (neg_respecte h))

def Zr.mul : Zr → Zr → Zr :=
  Quotient.lift₂ (fun p q => Zr.mk (p.1 * q.1 + p.2 * q.2) (p.1 * q.2 + p.2 * q.1))
    (fun ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ h1 h2 => Zr.mk_eq_mk.mpr (mul_respecte h1 h2))

instance : Add Zr := ⟨Zr.add⟩
instance : Neg Zr := ⟨Zr.neg⟩
instance : Mul Zr := ⟨Zr.mul⟩

theorem Zr.add_mk (a b c d : Nat) : Zr.mk a b + Zr.mk c d = Zr.mk (a + c) (b + d) := rfl
theorem Zr.neg_mk (a b : Nat) : -Zr.mk a b = Zr.mk b a := rfl
theorem Zr.mul_mk (a b c d : Nat) :
    Zr.mk a b * Zr.mk c d = Zr.mk (a * c + b * d) (a * d + b * c) := rfl

end Parcours.Constructions

#verifier
