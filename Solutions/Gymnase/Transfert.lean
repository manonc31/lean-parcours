/- @parcours
titre: Transporter un « il existe »
difficulte: 1
requiert: Gymnase.Temoin
indice: `obtain ⟨n, hn⟩ := h`, puis `exact ⟨n, hfg n hn⟩`.
-/
import ParcoursOutils

/-!
# Transporter un « il existe »

On récupère le témoin d'une hypothèse (`obtain ⟨n, hn⟩ := h`), et on le réutilise.

Le Gymnase : des petits exercices pour s'entraîner à un réflexe à la fois.
-/

namespace Parcours.Gymnase

theorem transport (f g : Nat → Nat) (h : ∃ n, f n = 0) (hfg : ∀ n, f n = 0 → g n = 1) :
    ∃ n, g n = 1 := by -- @exo
  obtain ⟨n, hn⟩ := h
  exact ⟨n, hfg n hn⟩

end Parcours.Gymnase

#verifier
