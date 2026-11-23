import ParcoursOutils

/-!
# Transporter un « il existe »

On récupère le témoin d'une hypothèse (`obtain ⟨n, hn⟩ := h`), et on le réutilise.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.

---
*Exercice* `Gymnase.Transfert` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Gymnase.Transfert` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Gymnase

theorem transport (f g : Nat → Nat) (h : ∃ n, f n = 0) (hfg : ∀ n, f n = 0 → g n = 1) :
    ∃ n, g n = 1 := by
  sorry

end Parcours.Gymnase

#verifier
