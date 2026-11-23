import Exercices.Naturels.Transfert

/-!
# La récurrence fonctionnelle

Pour une fonction récursive qui ne suit pas un schéma simple, `fun_induction f n with` fait une récurrence qui **suit les appels récursifs** de `f`. Ici `pas2` descend de 2 en 2.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.FunInduction` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Gymnase.FunInduction` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

def pas2 : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => pas2 n + 2

theorem pas2_eq (n : Nat) : pas2 n = n := by
  sorry

end Parcours.Gymnase

#verifier
