/- @parcours
titre: Somme de limites et gendarmes
difficulte: 3
indice: `somme_limites` : le grand classique « ε/2 ». Applique les hypothèses avec `ε / 2`, prends `max N N'`, et l'inégalité triangulaire.
indice: `gendarmes` : à partir du rang `max N N'`, `l - ε < u n ≤ v n ≤ w n < l + ε`. Utilise `vabs_lt` dans les deux sens.
-/
import Solutions.Analyse.ValeurAbsolue

/-!
# Somme de limites et théorème des gendarmes

## À prouver
1. `somme_limites : Tend u a → Tend v b → Tend (fun n => u n + v n) (a + b)`
2. `gendarmes` : si `u n ≤ v n ≤ w n` et si `u` et `w` tendent vers `l`, alors `v` aussi.

## Ressources
- [Théorème des gendarmes (Wikipédia)](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_des_gendarmes)
-/

namespace Parcours.Analyse

theorem somme_limites {u v : Suite} {a b : Rat} (hu : Tend u a) (hv : Tend v b) :
    Tend (fun n => u n + v n) (a + b) := by -- @exo
  intro ε hε
  obtain ⟨N, hN⟩ := hu (ε / 2) (by grind)
  obtain ⟨N', hN'⟩ := hv (ε / 2) (by grind)
  refine ⟨max N N', fun n hn => ?_⟩
  have h1 := hN n (by omega)
  have h2 := hN' n (by omega)
  have t := inegalite_triangulaire (u n - a) (v n - b)
  have e : u n - a + (v n - b) = u n + v n - (a + b) := by grind
  rw [e] at t
  show vabs (u n + v n - (a + b)) < ε
  grind

theorem gendarmes {u v w : Suite} {l : Rat} (hu : Tend u l) (hw : Tend w l)
    (h1 : ∀ n, u n ≤ v n) (h2 : ∀ n, v n ≤ w n) : Tend v l := by -- @exo
  intro ε hε
  obtain ⟨N, hN⟩ := hu ε hε
  obtain ⟨N', hN'⟩ := hw ε hε
  refine ⟨max N N', fun n hn => ?_⟩
  have a := (vabs_lt _ _).mp (hN n (by omega))
  have b := (vabs_lt _ _).mp (hN' n (by omega))
  have c1 := h1 n
  have c2 := h2 n
  rw [vabs_lt]
  constructor <;> grind

end Parcours.Analyse

#verifier
