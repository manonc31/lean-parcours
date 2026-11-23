/- @parcours
titre: Négation et quantificateurs
difficulte: 3
requiert: Logique.Existe, Logique.Classique
indice: `non_existe` est constructif : `constructor`, puis `intro h x hx` dans un sens et `rintro h ⟨x, hx⟩` dans l'autre.
indice: `non_pourtout`, sens `→` : raisonne par l'absurde avec `apply Classical.byContradiction` puis `intro hne` (où `hne : ¬∃ x, ¬p x`).
indice: Ensuite il faut prouver `∀ x, p x` (pour contredire `h`) : pour chaque `x`, encore un raisonnement par l'absurde.
-/
import Solutions.Logique.Classique

/-!
# Négation et quantificateurs

« Il n'existe pas de x tel que p(x) » ⟺ « pour tout x, non p(x) ». C'est constructif.

« Ce n'est pas vrai que tout x vérifie p » ⟺ « il existe un x qui ne vérifie pas p ».
Le sens `→` demande la logique classique : on affirme l'existence d'un `x` sans savoir le construire !

## À prouver
1. `non_existe : (¬∃ x, p x) ↔ ∀ x, ¬p x`
2. `non_pourtout : (¬∀ x, p x) ↔ ∃ x, ¬p x`
-/

namespace Parcours.Logique

variable {α : Type} {p : α → Prop}

theorem non_existe : (¬∃ x, p x) ↔ ∀ x, ¬p x := by -- @exo
  constructor
  · intro h x hx
    exact h ⟨x, hx⟩
  · rintro h ⟨x, hx⟩
    exact h x hx

theorem non_pourtout : (¬∀ x, p x) ↔ ∃ x, ¬p x := by -- @exo
  constructor
  · intro h
    apply Classical.byContradiction
    intro hne
    apply h
    intro x
    apply Classical.byContradiction
    intro hnp
    exact hne ⟨x, hnp⟩
  · rintro ⟨x, hnp⟩ h
    exact hnp (h x)

end Parcours.Logique

#verifier
