import ParcoursOutils

/-!
# Deux fonctions égales

Deux fonctions sont égales si elles donnent le même résultat partout : `funext x` transforme le but `f = g` en `f x = g x`.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.Funext` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Gymnase.Funext` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem funext_exemple (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := by
  sorry

theorem composee : (fun x : Nat => x + 1) ∘ (fun x => 2 * x) = fun x => 2 * x + 1 := by
  sorry

end Parcours.Gymnase

#verifier
