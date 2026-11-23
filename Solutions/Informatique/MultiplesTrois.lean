/- @parcours
titre: L'automate des multiples de 3
difficulte: 2
requiert: Informatique.Automates
indice: `lire_mod` : récurrence sur `w` en généralisant l'état `e` et la valeur `v`.
indice: Le pas : `(2 (v mod 3) + b) mod 3 = (2v + b) mod 3` : `omega`.
-/
import Solutions.Informatique.Automates

/-!
# L'automate des multiples de 3

Un automate qui lit un nombre écrit en binaire (bit de poids fort en premier) et dit s'il est
multiple de 3, avec seulement **3 états** : le reste modulo 3 de ce qui a été lu. Lire un bit `b`
fait passer de la valeur `v` à `2v + b`, donc du reste `e` au reste `(2e + b) mod 3`.

## À prouver
1. `lire_mod` : après avoir lu `w`, l'automate est dans l'état « valeur de `w` modulo 3 ».
2. `multiple3_correct : multiple3.accepte w = (valeurBin w 0 % 3 == 0)`
3. `neuf : multiple3.accepte [true, false, false, true] = true` (1001 = 9)
-/

namespace Parcours.Info

/-- La valeur d'un mot binaire, bit de poids fort en premier (`v` : valeur déjà lue). -/
def valeurBin : List Bool → Nat → Nat
  | [], v => v
  | b :: w, v => valeurBin w (2 * v + b.toNat)

def multiple3 : Automate Nat Bool := ⟨0, fun e b => (2 * e + b.toNat) % 3, fun e => e == 0⟩

theorem lire_mod (w : List Bool) (e v : Nat) (h : e = v % 3) :
    multiple3.lire e w = valeurBin w v % 3 := by -- @exo
  induction w generalizing e v with
  | nil => simp [Automate.lire, valeurBin, h]
  | cons b w ih =>
    simp only [Automate.lire, valeurBin]
    apply ih
    simp only [multiple3]
    omega

theorem multiple3_correct (w : List Bool) : multiple3.accepte w = (valeurBin w 0 % 3 == 0) := by -- @exo
  unfold Automate.accepte
  rw [show multiple3.init = 0 from rfl, lire_mod w 0 0 rfl]
  rfl

theorem neuf : multiple3.accepte [true, false, false, true] = true := by -- @exo
  decide

end Parcours.Info

#verifier
