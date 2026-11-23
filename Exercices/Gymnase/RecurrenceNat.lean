import Exercices.Naturels.Transfert

/-!
# Une récurrence sur Nat

On définit `double n` par récurrence (`double 0 = 0`, `double (n+1) = double n + 2`). Prouve que `double n = 2 * n` : `induction n with`, puis dans le cas `succ`, déplie la définition (`rw [double]` ou `simp only [double]`) et utilise `ih` et `omega`.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.RecurrenceNat` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Gymnase.RecurrenceNat` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

def double : Nat → Nat
  | 0 => 0
  | n + 1 => double n + 2

theorem double_eq (n : Nat) : double n = 2 * n := by
  sorry

end Parcours.Gymnase

#verifier
