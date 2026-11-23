import Exercices.Programmes.Definitions

/-!
# Chercher un mot dans un texte

Le Ctrl+F de ton éditeur : chercher la première position où un motif apparaît dans un texte.
Version naïve : on essaie chaque position, et on regarde si le texte **commence par** le motif.

## À prouver
1. `commencePar_spec : commencePar m t = true ↔ m <+: t` (`<+:` : « est un préfixe de »)
2. `trouve_correct` : si on trouve la position `j`, le motif est bien là.
3. `absent_correct` : si on ne trouve rien, le motif n'apparaît nulle part.
4. `exemple_motif : chercherMotif [1, 2] [3, 1, 1, 2, 5] 0 = some 2`

## Ressources
- [Algorithme de recherche de sous-chaîne (Wikipédia)](https://fr.wikipedia.org/wiki/Algorithme_de_recherche_de_sous-cha%C3%AEne)

---
*Exercice* `Programmes.Motif` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Programmes.Motif` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Prog

def commencePar : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: m, b :: t => a == b && commencePar m t

/-- `chercherMotif m t i` : première position (comptée à partir de `i`) où `m` apparaît dans `t`. -/
def chercherMotif (m : List Nat) : List Nat → Nat → Option Nat
  | [], i => if m.isEmpty then some i else none
  | b :: t, i => if commencePar m (b :: t) then some i else chercherMotif m t (i + 1)

theorem commencePar_spec (m t : List Nat) : commencePar m t = true ↔ m <+: t := by
  sorry

theorem trouve_correct (m t : List Nat) (i j : Nat) (h : chercherMotif m t i = some j) :
    i ≤ j ∧ m <+: t.drop (j - i) := by
  sorry

theorem absent_correct (m t : List Nat) (i : Nat) (h : chercherMotif m t i = none) :
    ∀ k, ¬ m <+: t.drop k := by
  sorry

theorem exemple_motif : chercherMotif [1, 2] [3, 1, 1, 2, 5] 0 = some 2 := by
  sorry

end Parcours.Prog

#verifier
