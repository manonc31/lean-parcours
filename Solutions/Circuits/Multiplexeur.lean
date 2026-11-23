/- @parcours
titre: Le multiplexeur
difficulte: 1
requiert: Circuits.Nand
indice: `mux_ok` : tous les cas.
indice: `mux4_ok` : quatre cas pour la sélection, puis `simp [mux4, mux_ok]`.
-/
import Solutions.Circuits.Definitions

/-!
# Le multiplexeur

Un **multiplexeur** est un aiguillage : un bit de sélection `s` choisit laquelle des deux entrées
passe à la sortie. Avec deux bits de sélection et trois multiplexeurs, on choisit parmi 4 entrées :
c'est ainsi qu'un processeur lit une case de mémoire à partir de son adresse.

## À prouver
1. `mux_ok : mux s a b = if s then b else a`
2. `mux4_ok` : le multiplexeur à 4 entrées choisit l'entrée numéro `2 s₁ + s₀`.
-/

namespace Parcours.Circuits

def mux (s a b : Bool) : Bool := (!s && a) || (s && b)

def mux4 (s1 s0 a b c d : Bool) : Bool := mux s1 (mux s0 a b) (mux s0 c d)

theorem mux_ok (s a b : Bool) : mux s a b = if s then b else a := by -- @exo
  cases s <;> cases a <;> cases b <;> rfl

theorem mux4_ok (s1 s0 a b c d : Bool) :
    mux4 s1 s0 a b c d = [a, b, c, d].getD (2 * s1.toNat + s0.toNat) false := by -- @exo
  cases s1 <;> cases s0 <;> simp [mux4, mux_ok]

end Parcours.Circuits

#verifier
